// ==============================================================
//  XIAO ESP32-S3 — ECG + SpO2 + Activity + OLED + Firebase
//  v4 — Full Firebase Realtime Database Integration
// ==============================================================

#include <Arduino.h>
#include <Wire.h>
#include <math.h>
#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <MAX30105.h>
#include <heartRate.h>
#include <FirebaseESP32.h>
#include <WiFi.h>

// ── Pins ──────────────────────────────────────────────────────
#define ECG_PIN    A0
#define LO_PLUS     2
#define LO_MINUS    3
#define PIN_SDA     5
#define PIN_SCL     6

// ── WiFi + Firebase ───────────────────────────────────────────
#define WIFI_SSID     "1+"
#define WIFI_PASSWORD "q3bg2sug"
#define DATABASE_URL  "https://ecg-monitor-default-rtdb.firebaseio.com/"

FirebaseData fbdo;
FirebaseAuth auth;
FirebaseConfig config;

// Non-blocking Firebase send timer
unsigned long lastFirebaseMs = 0;
#define FIREBASE_INTERVAL_MS 1000   // push to DB every 1 second

// ── OLED ──────────────────────────────────────────────────────
#define SCREEN_WIDTH  128
#define SCREEN_HEIGHT  64
#define OLED_ADDR    0x3C
Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, -1);

// ── MAX30102 ──────────────────────────────────────────────────
MAX30105 particleSensor;
const byte RATE_SIZE = 4;
byte  rates[RATE_SIZE] = {0};
byte  rateSpot  = 0;
long  lastBeat  = 0;
int   rawMaxBPM = 0;

int   spo2Buffer[RATE_SIZE] = {0};
byte  spo2Spot   = 0;
int   stableSpO2 = 0;

int   stableBPM       = 0;
int   candidateBPM    = 0;
unsigned long candidateStartMs = 0;
#define STABLE_HOLD_MS  1000
#define MAX_BPM_JUMP    20

bool fingerOn = false;

// ── MPU6050 ───────────────────────────────────────────────────
#define MPU_ADDR  0x68
#define MPU_PWR   0x6B
#define MPU_ACC   0x3B
float ax_ref = 0, ay_ref = 0, az_ref = 0;
const int MOT_N = 30;
float motionBuffer[MOT_N];
int   motionIndex = 0;
float avgMotion   = 0;
#define ACT_LOW  0
#define ACT_MOD  1
#define ACT_HIGH 2
int activityLevel = ACT_LOW;
int prevActivity  = ACT_LOW;

// ── ECG ───────────────────────────────────────────────────────
float ecg_alpha    = 0.08f;
float ecg_filtered = 2000.0f;
float ecg_baseline = 2000.0f;
#define PEAK_THRESHOLD  300
#define REFRACTORY_MS   300
#define RR_BUF_SIZE      12
unsigned long rr_buf[RR_BUF_SIZE];
uint8_t  rr_idx   = 0;
uint8_t  rr_count = 0;
int      ecgBPM   = 0;
bool     above_thresh    = false;
int      peak_val        = 0;
unsigned long peak_time_ms   = 0;
unsigned long last_beat_ms   = 0;
unsigned long refractory_end = 0;
unsigned long next_sample_ms = 0;
#define SAMPLE_MS 4

// ── Timers ────────────────────────────────────────────────────
unsigned long last_display_ms = 0;
unsigned long last_serial_ms  = 0;
#define DISPLAY_MS  500
#define SERIAL_MS  1000

// =============================================================
//  HRV — SDNN from ECG RR buffer
// =============================================================
int computeHRV() {
    if (rr_count < 4) return 0;
    uint8_t n = (rr_count < RR_BUF_SIZE) ? rr_count : RR_BUF_SIZE;
    float mean = 0;
    for (uint8_t i = 0; i < n; i++) mean += rr_buf[i];
    mean /= n;
    float variance = 0;
    for (uint8_t i = 0; i < n; i++) {
        float d = rr_buf[i] - mean;
        variance += d * d;
    }
    return (int)sqrtf(variance / n);  // SDNN in ms
}

// =============================================================
//  MPU6050
// =============================================================
bool mpuWakeup() {
    Wire.beginTransmission(MPU_ADDR);
    Wire.write(MPU_PWR);
    Wire.write(0x00);
    return (Wire.endTransmission(true) == 0);
}

void readAccel(float &ax, float &ay, float &az) {
    Wire.beginTransmission(MPU_ADDR);
    Wire.write(MPU_ACC);
    Wire.endTransmission(false);
    Wire.requestFrom((uint8_t)MPU_ADDR, (uint8_t)6);
    int16_t rx = (Wire.read() << 8) | Wire.read();
    int16_t ry = (Wire.read() << 8) | Wire.read();
    int16_t rz = (Wire.read() << 8) | Wire.read();
    ax = rx / 16384.0f;
    ay = ry / 16384.0f;
    az = rz / 16384.0f;
}

void calibrateMPU() {
    float ax, ay, az;
    for (int i = 0; i < 200; i++) {
        readAccel(ax, ay, az);
        ax_ref += ax; ay_ref += ay; az_ref += az;
        delay(5);
    }
    ax_ref /= 200; ay_ref /= 200; az_ref /= 200;
    for (int i = 0; i < MOT_N; i++) motionBuffer[i] = 0;
}

void updateActivity(float ax, float ay, float az) {
    float motion = sqrtf(
        (ax-ax_ref)*(ax-ax_ref) +
        (ay-ay_ref)*(ay-ay_ref) +
        (az-az_ref)*(az-az_ref)
    );
    motionBuffer[motionIndex] = motion;
    motionIndex = (motionIndex + 1) % MOT_N;
    avgMotion = 0;
    for (int i = 0; i < MOT_N; i++) avgMotion += motionBuffer[i];
    avgMotion /= MOT_N;

    if      (avgMotion < 0.30f) activityLevel = ACT_LOW;
    else if (avgMotion < 0.80f) activityLevel = ACT_MOD;
    else                        activityLevel = ACT_HIGH;
}

const char* activityStr() {
    switch (activityLevel) {
        case ACT_HIGH: return "HIGH";
        case ACT_MOD:  return "MOD";
        default:       return "LOW";
    }
}

// =============================================================
//  Stable BPM
// =============================================================
void updateStableBPM(int newRaw, unsigned long now)
{
    if (newRaw < 40 || newRaw > 200) return;

    if (stableBPM == 0)
    {
        stableBPM = newRaw;
        candidateBPM = newRaw;
        candidateStartMs = now;
        return;
    }

    if (abs(newRaw - stableBPM) <= MAX_BPM_JUMP)
    {
        if (abs(newRaw - candidateBPM) <= MAX_BPM_JUMP)
        {
            if (now - candidateStartMs >= STABLE_HOLD_MS)
                stableBPM = newRaw;
        }
        else
        {
            candidateBPM = newRaw;
            candidateStartMs = now;
        }
    }
}

// =============================================================
//  ECG
// =============================================================
bool ecgIsValid(int v) { return (v > 200 && v < 3800); }

int computeECGBPM() {
    if (rr_count == 0) return 0;
    unsigned long sum = 0;
    uint8_t n = (rr_count < RR_BUF_SIZE) ? rr_count : RR_BUF_SIZE;
    for (uint8_t i = 0; i < n; i++) sum += rr_buf[i];
    return (int)(60000.0f / ((float)sum / n));
}

void detectECGPeak(int val, unsigned long now_ms) {
    if (val >= PEAK_THRESHOLD) {
        if (!above_thresh) {
            above_thresh = true; peak_val = val; peak_time_ms = now_ms;
        } else if (val > peak_val) {
            peak_val = val; peak_time_ms = now_ms;
        }
    } else {
        if (above_thresh) {
            above_thresh = false;
            if (now_ms >= refractory_end) {
                if (last_beat_ms > 0) {
                    unsigned long rr = peak_time_ms - last_beat_ms;
                    if (rr >= 270 && rr <= 2400) {
                        rr_buf[rr_idx % RR_BUF_SIZE] = rr;
                        rr_idx++;
                        if (rr_count < RR_BUF_SIZE) rr_count++;
                        ecgBPM = computeECGBPM();
                    }
                }
                last_beat_ms   = peak_time_ms;
                refractory_end = now_ms + REFRACTORY_MS;
            }
            peak_val = 0;
        }
    }
}

// =============================================================
//  Smart Status
// =============================================================
int getSmartStatus(int bpm) {
    if (bpm <= 0) return 1;
    if (bpm < 60) return 0;
    int hi = (activityLevel == ACT_HIGH) ? 160 :
             (activityLevel == ACT_MOD)  ? 120 : 100;
    return (bpm > hi) ? 2 : 1;
}

// =============================================================
//  OLED
// =============================================================
void updateOLED(int bpm, int o2Value, int status) {
    display.clearDisplay();
    display.setTextColor(SSD1306_WHITE);
    display.drawFastHLine(0, 11, 128, SSD1306_WHITE);
    display.setTextSize(1);
    display.setCursor(4, 1);
    display.print("ECG MONITOR");

    display.setTextSize(2);
    display.setCursor(0, 18);
    if (bpm == 0) display.print("HR: --");
    else { display.print("HR: "); display.print(bpm); }

    display.setCursor(0, 36);
    if (!fingerOn || o2Value == 0) display.print("O2: --");
    else { display.print("O2: "); display.print(o2Value); display.print("%"); }

    display.drawFastVLine(78, 12, 38, SSD1306_WHITE);
    display.setTextSize(1);
    display.setCursor(84, 18); display.print("ACTV:");
    display.setCursor(84, 28); display.print(activityStr());
    display.setCursor(84, 40); display.print("M:"); display.print(avgMotion, 1);

    display.drawFastHLine(0, 51, 128, SSD1306_WHITE);
    display.setCursor(4, 54);
    switch (status) {
        case 0: display.print("ALERT: LOW PULSE RATE");    break;
        case 2: display.print("WARNING: HIGH ACCEL PULSE"); break;
        default:
            if (fingerOn && o2Value < 95 && o2Value > 0)
                display.print("ALERT: HYPOXIA");
            else
                display.print("STATUS: OPERATIONAL");
            break;
    }
    display.display();
}

// =============================================================
//  ★ Firebase — push all vitals as one JSON object ★
// =============================================================
void pushToFirebase(int displayBPM, int status) {

    // Determine ECG status string
    const char* ecgStatus;
    if (!fingerOn && ecgBPM == 0)  ecgStatus = "No Signal";
    else if (status == 0)          ecgStatus = "Low";
    else if (status == 2)          ecgStatus = "High";
    else                           ecgStatus = "Normal";

    bool fallDetected = (activityLevel == ACT_HIGH && avgMotion > 1.5f);
    int  hrv          = computeHRV();

    // Build a FirebaseJson object — one atomic write to /vitals
    FirebaseJson json;
    json.set("heartRate",    displayBPM);
    json.set("ecgBPM",       ecgBPM);
    json.set("spo2",         stableSpO2);
    json.set("hrv",          hrv);
    json.set("activity",     activityStr());
    json.set("motionIndex",  avgMotion);
    json.set("ecgStatus",    ecgStatus);
    json.set("fallDetected", fallDetected);
    json.set("fingerOn",     fingerOn);
    json.set("status",       status);

    if (Firebase.updateNode(fbdo, "/latestData", json)) {
        Serial.println("[Firebase] Push OK");
    } else {
        Serial.print("[Firebase] FAIL: ");
        Serial.println(fbdo.errorReason());
    }
}

// =============================================================
//  Setup
// =============================================================
void setup() {
    Serial.begin(115200);
    uint32_t t0 = millis();
    while (!Serial && millis() - t0 < 2000) {}

    pinMode(LO_PLUS,  INPUT);
    pinMode(LO_MINUS, INPUT);

    Wire.begin(PIN_SDA, PIN_SCL);
    Wire.setClock(400000);

    // OLED init
    if (!display.begin(SSD1306_SWITCHCAPVCC, OLED_ADDR))
        Serial.println("OLED FAIL");
    display.clearDisplay();
    display.setTextSize(1);
    display.setTextColor(SSD1306_WHITE);
    display.setCursor(0, 0); display.println("Booting Smart Hub...");
    display.display();

    // MAX30102
    display.setCursor(0, 16);
    if (particleSensor.begin(Wire, I2C_SPEED_FAST, 0x57)) {
        particleSensor.setup(0x1F, 4, 2, 400, 411, 4096);
        display.println("MAX30102 Setup: OK");
        Serial.println("MAX30102 OK");
    } else {
        display.println("MAX30102 Setup: FAIL");
        Serial.println("MAX30102 FAIL");
    }
    display.display(); delay(400);

    // MPU6050
    display.setCursor(0, 32);
    if (mpuWakeup()) {
        display.println("MPU6050 Sensor: OK");
        display.setCursor(0, 48); display.println("Calibrating IMU...");
        display.display();
        calibrateMPU();
        display.setCursor(0, 48); display.println("Calibration Done!");
        Serial.println("MPU6050 OK");
    } else {
        display.println("MPU6050 Sensor: FAIL");
        Serial.println("MPU6050 FAIL");
    }
    display.display(); delay(800);

    // WiFi
    display.setCursor(0, 0); display.clearDisplay();
    display.println("Connecting WiFi...");
    display.display();
    WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
    Serial.println("Connecting to WiFi...");

    WiFi.begin(WIFI_SSID, WIFI_PASSWORD);

    int attempts = 0;

    while (WiFi.status() != WL_CONNECTED && attempts < 20)
    {
        delay(1000);
        Serial.print(".");
        attempts++;
    }

    Serial.println();

    if (WiFi.status() == WL_CONNECTED)
    {
        Serial.println("WiFi Connected");
        Serial.println(WiFi.localIP());
    }
    else
    {
        Serial.println("WiFi FAILED");
    }
    Serial.print("\nWiFi connected: ");
    Serial.println(WiFi.localIP());
    display.println("WiFi: Connected!");
    display.display();

    // Firebase
    config.database_url      = DATABASE_URL;
    config.signer.test_mode  = true;   // no auth — open rules required
    Firebase.begin(&config, &auth);
    Firebase.reconnectWiFi(true);
    Serial.println("Firebase Ready.");
    display.println("Firebase: Ready");
    display.display();
    delay(800);
}

// =============================================================
//  Loop
// =============================================================
void loop() {
    unsigned long now = millis();

    // ── ECG @ 250 Hz ─────────────────────────────────────────
    if (now >= next_sample_ms) {
        next_sample_ms = now + SAMPLE_MS;
        if (!digitalRead(LO_PLUS) && !digitalRead(LO_MINUS)) {
            int raw = analogRead(ECG_PIN);
            if (!ecgIsValid(raw)) raw = (int)ecg_filtered;
            ecg_filtered = (ecg_alpha * raw) + ((1.0f - ecg_alpha) * ecg_filtered);
            ecg_baseline = (0.002f * ecg_filtered) + (0.998f * ecg_baseline);
            int ecg    = (int)(ecg_filtered - ecg_baseline) + 2000;
            int output = constrain(map(ecg, 1400, 2600, 0, 999), 0, 999);
            detectECGPeak(output, now);
        }
    }

    // ── MAX30102 ─────────────────────────────────────────────
    long irValue  = particleSensor.getIR();
    long redValue = particleSensor.getRed();
    fingerOn = (irValue > 5000);

    if (fingerOn) {
        if (checkForBeat(irValue)) {
            long delta = now - lastBeat;
            lastBeat   = now;
            float bpm  = 60.0f / (delta / 1000.0f);
            if (bpm > 40.0f && bpm < 200.0f) {
                rates[rateSpot % RATE_SIZE] = (byte)bpm;
                rateSpot++;
                int s = 0;
                for (byte i = 0; i < RATE_SIZE; i++) s += rates[i];
                rawMaxBPM = s / RATE_SIZE;
                updateStableBPM(rawMaxBPM, now);
            }
        }
        if (redValue > 0 && irValue > 0) {
            float ratio    = (float)redValue / (float)irValue;
            float spo2Calc = constrain(110.0f - (25.0f * ratio), 70.0f, 100.0f);
            spo2Buffer[spo2Spot % RATE_SIZE] = (int)spo2Calc;
            spo2Spot++;
            long sum = 0;
            for (byte i = 0; i < RATE_SIZE; i++) sum += spo2Buffer[i];
            stableSpO2 = sum / RATE_SIZE;
        }
    } else {
        rawMaxBPM = 0; stableBPM = 0; stableSpO2 = 0;
        rateSpot  = 0; spo2Spot  = 0;
        for (byte i = 0; i < RATE_SIZE; i++) { rates[i] = 0; spo2Buffer[i] = 0; }
    }

    // ── MPU6050 ──────────────────────────────────────────────
    float ax, ay, az;
    readAccel(ax, ay, az);
    updateActivity(ax, ay, az);

    // ── Fusion ───────────────────────────────────────────────
    int displayBPM = fingerOn ? rawMaxBPM : ecgBPM;
    int status     = getSmartStatus(displayBPM);

    // ── OLED @ 500ms ─────────────────────────────────────────
    if (now - last_display_ms >= DISPLAY_MS) {
        last_display_ms = now;
        updateOLED(displayBPM, stableSpO2, status);
    }

    // ── Firebase @ 1s (non-blocking timer) ───────────────────
    if (now - lastFirebaseMs >= FIREBASE_INTERVAL_MS) {
        lastFirebaseMs = now;
        if (WiFi.status() == WL_CONNECTED) {
            pushToFirebase(displayBPM, status);
        } else {
            Serial.println("[WiFi] Disconnected — reconnecting...");
            WiFi.begin(WIFI_SSID, WIFI_PASSWORD);
        }
    }

    // ── Serial @ 1s ──────────────────────────────────────────
    if (now - last_serial_ms >= SERIAL_MS) {
        last_serial_ms = now;
        Serial.println("==========================================");
        Serial.printf("ECG BPM   : %d\n", ecgBPM);
        Serial.printf("MAX BPM   : %d\n", stableBPM);
        Serial.printf("ECG BPM   : %d\n", ecgBPM);
        Serial.printf("Pulse BPM : %d\n", stableBPM);     
        Serial.printf("SpO2      : %d%%\n", stableSpO2);
        Serial.printf("HRV(SDNN) : %d ms\n", computeHRV());
        Serial.printf("Activity  : %s (%.2f)\n", activityStr(), avgMotion);
        Serial.printf("Status    : %d\n", status);
        Serial.println("==========================================");
    }
}