#!/usr/bin/env python3
"""
Conflict Monitor RSS Server
----------------------------
Fetches BBC Middle East + Al Jazeera RSS feeds.
Extracts location via gazetteer, event type via keyword rules + RSS categories.
Serves /latest.json on port 8766.

Usage:  python3 rss-server.py
        Then open conflict-monitor.html
"""

import time, threading, logging, json, re, hashlib
import urllib.request
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime, timezone, timedelta
from email.utils import parsedate_to_datetime
from xml.etree import ElementTree as ET
from html.parser import HTMLParser

# ── spaCy — lazy-loaded for NER geolocation + negation-aware severity ─────────
_nlp = None   # loaded on first use so server starts even if model not installed

def _get_nlp():
    global _nlp
    if _nlp is not None:
        return _nlp
    try:
        import spacy
        _nlp = spacy.load("en_core_web_sm")
        log.info("spaCy en_core_web_sm loaded — NER geolocation active")
    except Exception as e:
        log.warning("spaCy not available (%s) — falling back to gazetteer-only", e)
        _nlp = False   # False = tried and failed, don't retry every article
    return _nlp

# Source credibility weights for severity adjustment
# Iranian state sources over-use escalatory vocabulary — discount one tier
_SOURCE_DISCOUNT = {"Mehr News", "Tehran Times", "IRNA"}

# Hedging verbs that indicate unconfirmed/reported events — drop one severity tier
_HEDGE_VERBS = {
    "claim","claims","claimed","report","reports","reported","allege","alleges",
    "alleged","say","says","said","suggest","suggests","suggested","warn","warns",
    "warned","deny","denies","denied","accuse","accuses","accused",
}

# Negation tokens spaCy uses
_NEG_DEPS = {"neg"}


PORT        = 8766
DATA_DIR    = Path(__file__).parent / "rss_data"
LATEST_FILE = DATA_DIR / "latest.json"
ISW_FILE    = DATA_DIR / "isw.json"
STATUS_FILE = DATA_DIR / "status.json"
SEEN_FILE   = DATA_DIR / "seen_urls.json"
RETAIN_DAYS = 7       # keep events published within this many days
HEADERS     = {"User-Agent": "Mozilla/5.0 (compatible; ConflictMonitor/1.0)"}

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S"
)
log = logging.getLogger("rss")

# ── Feeds ─────────────────────────────────────────────────────────────────────
FEEDS = [
    {
        "name":        "Al Jazeera",
        "urls":        ["https://www.aljazeera.com/xml/rss/all.xml"],
        "credibility": 4,
        "region":      "ME",
        "bias":        "neutral-ME",
    },
    {
        "name":        "BBC Middle East",
        "urls":        ["https://feeds.bbci.co.uk/news/world/middle_east/rss.xml"],
        "credibility": 5,
        "region":      "ME",
        "bias":        "neutral-West",
    },
    {
        "name":        "Times of Israel",
        "urls":        [
            "https://www.timesofisrael.com/feed/",
            "https://www.timesofisrael.com/feed",
        ],
        "credibility": 4,
        "region":      "ME",
        "bias":        "israeli",
    },
    {
        "name":        "Haaretz",
        "urls":        [
            "https://www.haaretz.com/srv/middle-east-rss",
            "https://www.haaretz.com/srv/middle-east-news-rss",
            "https://www.haaretz.com/srv/haaretz-latest-rss",
        ],
        "credibility": 4,
        "region":      "ME",
        "bias":        "israeli",
    },

    {
        "name":        "Reuters",
        "urls":        [
            "https://news.google.com/rss/search?q=site:reuters.com+middle+east+war&hl=en-US&gl=US&ceid=US:en",
            "https://news.google.com/rss/search?q=site:reuters.com+iran+israel+gaza&hl=en-US&gl=US&ceid=US:en",
        ],
        "credibility": 5,
        "region":      "ME",
        "bias":        "neutral-West",
        "gnews":       True,
    },
    {
        "name":        "AP News",
        "urls":        [
            "https://news.google.com/rss/search?q=site:apnews.com+middle+east+war&hl=en-US&gl=US&ceid=US:en",
            "https://news.google.com/rss/search?q=site:apnews.com+iran+israel+gaza&hl=en-US&gl=US&ceid=US:en",
        ],
        "credibility": 5,
        "region":      "ME",
        "bias":        "neutral-West",
        "gnews":       True,
    },
    # ── Mehr News Agency (MNA — Iranian gov't semi-official wire) ───────────────
    # Highest-volume English Iranian outlet. Covers military ops in real-time.
    # Owned by Islamic Development Organization; director appointed by Supreme Leader.
    {
        "name":        "Mehr News",
        "urls":        [
            "https://news.google.com/rss/search?q=site:en.mehrnews.com+Iran+military+OR+strike+OR+missile&hl=en-US&gl=US&ceid=US:en",
            "https://news.google.com/rss/search?q=site:en.mehrnews.com+Middle+East+OR+Gaza+OR+Lebanon&hl=en-US&gl=US&ceid=US:en",
            "https://en.mehrnews.com/rss",
        ],
        "credibility": 2,
        "region":      "ME",
        "bias":        "iranian-state",
        "gnews":       True,
        "optional":    True,
    },
    # ── Tehran Times (Iranian state-controlled English daily) ─────────────────
    # Founded 1979 as "voice of the Islamic Revolution". More analytical than MNA.
    # Run by same management as Mehr News Agency since 2002.
    {
        "name":        "Tehran Times",
        "urls":        [
            "https://news.google.com/rss/search?q=site:tehrantimes.com+Iran+military+OR+nuclear+OR+Middle+East&hl=en-US&gl=US&ceid=US:en",
            "https://news.google.com/rss/search?q=site:tehrantimes.com+Gaza+OR+Lebanon+OR+Yemen+OR+Iraq&hl=en-US&gl=US&ceid=US:en",
            "https://www.tehrantimes.com/rss",
        ],
        "credibility": 2,
        "region":      "ME",
        "bias":        "iranian-state",
        "gnews":       True,
        "optional":    True,
    },
        # ── IRNA English (Islamic Republic News Agency — Iranian state media) ──────
    # Official Iranian government wire. Direct domain unreachable during active strikes.
    # Google News proxy indexes IRNA articles reliably from cached copies.
    {
        "name":          "IRNA",
        "urls":          [
            "https://news.google.com/rss/search?q=site:irna.ir+Iran+military+OR+nuclear+OR+sanctions&hl=en-US&gl=US&ceid=US:en",
            "https://news.google.com/rss/search?q=IRNA+Iran+Middle+East+attack+OR+strike+OR+missile&hl=en-US&gl=US&ceid=US:en",
            "https://en.irna.ir/rss",
            "https://en.irna.ir/rss.xml",
        ],
        "credibility":   3,
        "region":        "ME",
        "bias":          "iranian-state",
        "gnews":         True,
        "optional":      True,
        "domain_filter": ["irna.ir"],
    },
]

# ── Gazetteer: place name → (ISO country, lat, lng) ──────────────────────────
# Gazetteer entry format: "Name": (country_iso, lat, lng, type)
# Types (specificity order, highest first): site, crossing, district, city, region, water, country
GAZETTEER = {

    # ── Gaza Strip ────────────────────────────────────────────────────────────
    # Districts / camps
    "Jabalia":              ("PS", 31.533,  34.483, "district"),
    "Jabaliya":             ("PS", 31.533,  34.483, "district"),
    "Beit Lahiya":          ("PS", 31.558,  34.499, "district"),
    "Beit Hanoun":          ("PS", 31.531,  34.527, "district"),
    "Shujaiya":             ("PS", 31.499,  34.491, "district"),
    "Nuseirat":             ("PS", 31.442,  34.373, "district"),
    "Bureij":               ("PS", 31.437,  34.388, "district"),
    "Maghazi":              ("PS", 31.422,  34.376, "district"),
    "Deir al-Balah":        ("PS", 31.417,  34.350, "district"),
    "Khan Younis":          ("PS", 31.346,  34.306, "city"),
    "Khan Yunis":           ("PS", 31.346,  34.306, "city"),
    "Rafah":                ("PS", 31.287,  34.245, "city"),
    "Rafah crossing":       ("PS", 31.268,  34.225, "crossing"),
    "Kerem Shalom":         ("PS", 31.232,  34.267, "crossing"),
    "Erez crossing":        ("PS", 31.524,  34.499, "crossing"),
    "Gaza City":            ("PS", 31.501,  34.467, "city"),
    "Gaza Strip":           ("PS", 31.417,  34.313, "region"),
    "Gaza":                 ("PS", 31.417,  34.313, "region"),
    # West Bank
    "Jenin":                ("PS", 32.461,  35.293, "city"),
    "Jenin camp":           ("PS", 32.465,  35.296, "district"),
    "Nablus":               ("PS", 32.220,  35.254, "city"),
    "Tulkarm":              ("PS", 32.310,  35.028, "city"),
    "Hebron":               ("PS", 31.530,  35.099, "city"),
    "Ramallah":             ("PS", 31.899,  35.206, "city"),
    "Jericho":              ("PS", 31.857,  35.444, "city"),
    "Bethlehem":            ("PS", 31.705,  35.200, "city"),
    "Qalqilya":             ("PS", 32.188,  34.970, "city"),
    "Salfit":               ("PS", 32.085,  35.177, "city"),
    "Tubas":                ("PS", 32.320,  35.369, "city"),
    "West Bank":            ("PS", 31.952,  35.233, "region"),
    "Allenby Bridge":       ("PS", 31.882,  35.546, "crossing"),
    "Qalandia":             ("PS", 31.930,  35.228, "crossing"),

    # ── Israel ────────────────────────────────────────────────────────────────
    "Tel Aviv":             ("IL", 32.067,  34.783, "city"),
    "Jerusalem":            ("IL", 31.768,  35.214, "city"),
    "Haifa":                ("IL", 32.794,  34.990, "city"),
    "Eilat":                ("IL", 29.558,  34.952, "city"),
    "Ashkelon":             ("IL", 31.669,  34.571, "city"),
    "Ashdod":               ("IL", 31.793,  34.650, "city"),
    "Sderot":               ("IL", 31.524,  34.597, "city"),
    "Nahal Oz":             ("IL", 31.534,  34.556, "site"),
    "Be'er Sheva":          ("IL", 31.252,  34.791, "city"),
    "Beersheba":            ("IL", 31.252,  34.791, "city"),
    "Netanya":              ("IL", 32.329,  34.857, "city"),
    "Herzliya":             ("IL", 32.166,  34.843, "city"),
    "Dimona":               ("IL", 31.069,  35.034, "site"),
    "Nevatim":              ("IL", 31.208,  35.012, "site"),
    "Ramon airbase":        ("IL", 30.776,  34.667, "site"),
    "Palmachim":            ("IL", 31.897,  34.690, "site"),
    "Metula":               ("IL", 33.277,  35.572, "city"),
    "Kiryat Shmona":        ("IL", 33.207,  35.571, "city"),
    "Nahariya":             ("IL", 33.007,  35.098, "city"),
    "Safed":                ("IL", 32.965,  35.496, "city"),
    "Tiberias":             ("IL", 32.796,  35.531, "city"),
    "Golan Heights":        ("IL", 33.000,  35.750, "region"),
    "Golan":                ("IL", 33.000,  35.750, "region"),
    "northern Israel":      ("IL", 33.000,  35.500, "region"),
    "southern Israel":      ("IL", 31.000,  34.800, "region"),
    "Israel":               ("IL", 31.047,  34.852, "country"),

    # ── Lebanon ───────────────────────────────────────────────────────────────
    "Dahieh":               ("LB", 33.850,  35.490, "district"),
    "Dahiyeh":              ("LB", 33.850,  35.490, "district"),
    "Beirut southern suburb":("LB",33.850,  35.490, "district"),
    "Beirut":               ("LB", 33.889,  35.495, "city"),
    "Tyre":                 ("LB", 33.271,  35.194, "city"),
    "Sidon":                ("LB", 33.561,  35.371, "city"),
    "Tripoli":              ("LB", 34.436,  35.850, "city"),
    "Baalbek":              ("LB", 34.004,  36.211, "city"),
    "Nabatieh":             ("LB", 33.377,  35.484, "city"),
    "Khiam":                ("LB", 33.313,  35.612, "city"),
    "Bint Jbeil":           ("LB", 33.117,  35.431, "city"),
    "Marjayoun":            ("LB", 33.360,  35.592, "city"),
    "Bekaa Valley":         ("LB", 33.800,  36.000, "region"),
    "Bekaa":                ("LB", 33.800,  36.000, "region"),
    "South Lebanon":        ("LB", 33.272,  35.203, "region"),
    "southern Lebanon":     ("LB", 33.272,  35.203, "region"),
    "northern Lebanon":     ("LB", 34.200,  35.900, "region"),
    "Ain al-Hilweh":        ("LB", 33.544,  35.368, "district"),
    "Sabra":                ("LB", 33.872,  35.502, "district"),
    "Shatila":              ("LB", 33.872,  35.502, "district"),
    "Lebanon":              ("LB", 33.888,  35.495, "country"),

    # ── Syria ─────────────────────────────────────────────────────────────────
    "Damascus":             ("SY", 33.510,  36.292, "city"),
    "Aleppo":               ("SY", 36.202,  37.161, "city"),
    "Idlib":                ("SY", 35.930,  36.634, "city"),
    "Homs":                 ("SY", 34.727,  36.710, "city"),
    "Hama":                 ("SY", 35.130,  36.757, "city"),
    "Deir ez-Zor":          ("SY", 35.336,  40.141, "city"),
    "Raqqa":                ("SY", 35.952,  39.004, "city"),
    "Daraa":                ("SY", 32.617,  36.101, "city"),
    "Latakia":              ("SY", 35.524,  35.791, "city"),
    "Tartus":               ("SY", 34.889,  35.887, "city"),
    "Qamishli":             ("SY", 37.051,  41.227, "city"),
    "Hasaka":               ("SY", 36.484,  40.750, "city"),
    "Manbij":               ("SY", 36.511,  37.944, "city"),
    "Kobani":               ("SY", 36.892,  38.356, "city"),
    "Afrin":                ("SY", 36.514,  36.869, "city"),
    "Palmyra":              ("SY", 34.556,  38.283, "city"),
    "T4 airbase":           ("SY", 34.556,  37.622, "site"),
    "Tiyas airbase":        ("SY", 34.556,  37.622, "site"),
    "Shayrat airbase":      ("SY", 34.490,  36.910, "site"),
    "Mezzeh airbase":       ("SY", 33.478,  36.224, "site"),
    "Bab al-Hawa":          ("SY", 36.174,  36.604, "crossing"),
    "Nassib crossing":      ("SY", 33.000,  36.016, "crossing"),
    "eastern Syria":        ("SY", 35.500,  40.000, "region"),
    "northern Syria":       ("SY", 36.500,  37.500, "region"),
    "southern Syria":       ("SY", 32.800,  36.500, "region"),
    "Syria":                ("SY", 34.802,  38.997, "country"),

    # ── Iran ──────────────────────────────────────────────────────────────────
    # Nuclear / weapons sites
    "Natanz":               ("IR", 33.724,  51.926, "site"),
    "Fordow":               ("IR", 34.881,  50.993, "site"),
    "Arak":                 ("IR", 34.091,  49.689, "site"),
    "Parchin":              ("IR", 35.523,  51.783, "site"),
    "Bushehr":              ("IR", 28.921,  50.830, "site"),
    "Khondab":              ("IR", 34.091,  49.689, "site"),   # Arak heavy water
    "Lavizan":              ("IR", 35.754,  51.506, "site"),   # SPND campus
    "Mojdeh":               ("IR", 35.754,  51.506, "site"),   # Lavizan-2 / SPND
    "SPND":                 ("IR", 35.754,  51.506, "site"),   # nuke weaponisation
    # Tehran districts / IRGC compound sites
    "southeastern Tehran":  ("IR", 35.666,  51.480, "district"),
    "southwestern Tehran":  ("IR", 35.666,  51.340, "district"),
    "northwestern Tehran":  ("IR", 35.730,  51.300, "district"),
    "northern Tehran":      ("IR", 35.760,  51.420, "district"),
    "Sarallah Headquarters":("IR", 35.666,  51.480, "site"),
    "IRGC Headquarters":    ("IR", 35.666,  51.480, "site"),
    "Basij Headquarters":   ("IR", 35.666,  51.480, "site"),
    "Evin":                 ("IR", 35.754,  51.380, "site"),   # Evin prison
    "Mehrabad":             ("IR", 35.689,  51.313, "site"),   # airport / base
    "Imam Ali":             ("IR", 35.666,  51.480, "site"),   # IRGC battalion
    # Tehran city
    "Tehran":               ("IR", 35.694,  51.421, "city"),
    # Other major cities
    "Isfahan":              ("IR", 32.661,  51.680, "city"),
    "Mashhad":              ("IR", 36.297,  59.606, "city"),
    "Tabriz":               ("IR", 38.080,  46.299, "city"),
    "Ahvaz":                ("IR", 31.319,  48.671, "city"),
    "Shiraz":               ("IR", 29.592,  52.584, "city"),
    "Bandar Abbas":         ("IR", 27.189,  56.276, "city"),
    "Qom":                  ("IR", 34.639,  50.876, "city"),
    "Qum":                  ("IR", 34.639,  50.876, "city"),
    "Rasht":                ("IR", 37.281,  49.583, "city"),
    "Karaj":                ("IR", 35.835,  50.999, "city"),
    "Yazd":                 ("IR", 31.898,  54.368, "city"),
    "Kerman":               ("IR", 30.283,  57.079, "city"),
    "Zahedan":              ("IR", 29.496,  60.862, "city"),
    "Zabol":                ("IR", 31.029,  61.502, "city"),
    "Chabahar":             ("IR", 25.292,  60.643, "city"),
    "Dezful":               ("IR", 32.381,  48.399, "city"),
    "Khorramshar":          ("IR", 30.439,  48.181, "city"),
    "Abadan":               ("IR", 30.339,  48.304, "city"),
    "Bandar Imam Khomeini": ("IR", 30.415,  49.077, "city"),
    "Mahabad":              ("IR", 36.764,  45.723, "city"),   # Kurdish city
    "Sanandaj":             ("IR", 35.313,  46.996, "city"),   # Kurdistan capital
    "Ilam":                 ("IR", 33.637,  46.422, "city"),
    "Hamadan":              ("IR", 34.798,  48.515, "city"),
    "Kermanshah":           ("IR", 34.315,  47.065, "city"),
    "Urmia":                ("IR", 37.553,  45.076, "city"),
    "Ardabil":              ("IR", 38.247,  48.295, "city"),
    "Soltanabad":           ("IR", 33.500,  46.500, "city"),   # Ilam province
    # Provinces / regions
    "Sistan and Baluchistan":("IR",29.000,  59.000, "region"),
    "Sistan-Baluchestan":   ("IR", 29.000,  59.000, "region"),
    "Sistan":               ("IR", 30.500,  61.000, "region"),
    "Baluchistan":          ("IR", 27.500,  60.500, "region"),
    "Kurdistan province":   ("IR", 35.500,  46.500, "region"),
    "Iranian Kurdistan":    ("IR", 35.500,  46.500, "region"),
    "Khuzestan":            ("IR", 31.320,  48.670, "region"),
    "Ilam province":        ("IR", 33.200,  46.500, "region"),
    "Kermanshah province":  ("IR", 34.000,  46.500, "region"),
    "northwestern Iran":    ("IR", 37.000,  46.500, "region"),
    "western Iran":         ("IR", 34.000,  47.000, "region"),
    "southwestern Iran":    ("IR", 31.000,  49.000, "region"),
    "southeastern Iran":    ("IR", 29.000,  58.000, "region"),
    "eastern Iran":         ("IR", 33.000,  59.000, "region"),
    "southern Iran":        ("IR", 28.000,  55.000, "region"),
    "northern Iran":        ("IR", 37.000,  52.000, "region"),
    # Iranian military bases / airbases
    "Shahid Nojeh":         ("IR", 35.211,  48.652, "site"),   # Hamedan airbase
    "Hamedan airbase":      ("IR", 35.211,  48.652, "site"),
    "Bandar Abbas airbase": ("IR", 27.218,  56.378, "site"),
    "Tabriz airbase":       ("IR", 38.133,  46.235, "site"),
    "Dezful airbase":       ("IR", 32.434,  48.397, "site"),
    "Omidiyeh":             ("IR", 30.836,  49.535, "site"),
    "Shahrokhi":            ("IR", 34.581,  49.040, "site"),
    "Imam Ali airbase":     ("IR", 30.700,  48.800, "site"),
    "Khatam al-Anbiya":     ("IR", 35.694,  51.421, "site"),   # IRGC air HQ
    "Abuzar":               ("IR", 30.440,  49.687, "site"),
    # IRNA-relevant Persian Gulf islands & ports (appear in naval/sanctions stories)
    "Kharg Island":         ("IR", 29.238,  50.324, "site"),
    "Lavan Island":         ("IR", 26.807,  53.349, "site"),
    "Sirri Island":         ("IR", 25.900,  54.536, "site"),
    "Abu Musa":             ("IR", 25.877,  55.034, "site"),
    "Bandar Imam Khomeini": ("IR", 30.447,  49.077, "site"),
    "Bandar Mahshahr":      ("IR", 30.557,  49.198, "site"),
    "Chabahar":             ("IR", 25.292,  60.643, "city"),
    "Zahedan":              ("IR", 29.497,  60.862, "city"),
    "Kermanshah":           ("IR", 34.314,  47.065, "city"),
    "Khorramabad":          ("IR", 33.488,  48.356, "city"),
    "Ilam":                 ("IR", 33.637,  46.422, "city"),
    "Arak":                 ("IR", 34.094,  49.689, "city"),   # heavy water reactor
    "Fordow":               ("IR", 34.882,  50.569, "site"),   # enrichment site
    "Parchin":              ("IR", 35.525,  51.777, "site"),   # military complex
    "Strait of Hormuz":     ("IR", 26.567,  56.250, "water"),
    "Gulf of Oman":         ("IR", 24.000,  58.500, "water"),
    "Iran":                 ("IR", 32.427,  53.688, "country"),
    "Iranian":              ("IR", 32.427,  53.688, "country"),  # IRNA self-reference
    "Islamic Republic":     ("IR", 32.427,  53.688, "country"),  # IRNA formal name
    "IRGC":                 ("IR", 32.427,  53.688, "country"),  # Islamic Rev. Guard Corps
    "Supreme Leader":       ("IR", 35.694,  51.421, "city"),     # always Tehran
    "Persian Gulf":         ("IR", 27.000,  52.000, "water"),    # IRNA/regional coverage

    # ── Iraq ──────────────────────────────────────────────────────────────────
    # US bases / key sites
    "Ain al-Asad":          ("IQ", 33.786,  42.441, "site"),
    "Ain al-Assad":         ("IQ", 33.786,  42.441, "site"),
    "Erbil airbase":        ("IQ", 36.237,  43.963, "site"),
    "Harir airbase":        ("IQ", 36.534,  44.361, "site"),   # Kurdish region
    "Harir":                ("IQ", 36.534,  44.361, "site"),
    "Al-Bakr airfield":     ("IQ", 34.430,  43.590, "site"),   # Salah al-Din
    "Al-Bakr":              ("IQ", 34.430,  43.590, "site"),
    "Balad airbase":        ("IQ", 33.940,  44.361, "site"),
    "Al-Taji":              ("IQ", 33.521,  44.276, "site"),
    "Camp Victory":         ("IQ", 33.291,  44.347, "site"),
    "Green Zone":           ("IQ", 33.313,  44.386, "site"),
    # PMF / militia sites
    "Jurf al-Sakhar":       ("IQ", 32.669,  44.151, "site"),   # PMF stronghold
    "Jurf al-Nasr":         ("IQ", 32.669,  44.151, "site"),
    "Tharallah":            ("IQ", 33.313,  44.386, "site"),   # PMF HQ Baghdad
    "Abu Kamal":            ("IQ", 34.451,  40.919, "site"),   # Syria border
    # Cities
    "Baghdad":              ("IQ", 33.341,  44.401, "city"),
    "Mosul":                ("IQ", 36.340,  43.130, "city"),
    "Erbil":                ("IQ", 36.191,  44.009, "city"),
    "Basra":                ("IQ", 30.508,  47.783, "city"),
    "Kirkuk":               ("IQ", 35.467,  44.392, "city"),
    "Fallujah":             ("IQ", 33.350,  43.789, "city"),
    "Tikrit":               ("IQ", 34.596,  43.681, "city"),
    "Ramadi":               ("IQ", 33.426,  43.299, "city"),
    "Najaf":                ("IQ", 31.996,  44.330, "city"),
    "Karbala":              ("IQ", 32.616,  44.024, "city"),
    "Sulaymaniyah":         ("IQ", 35.557,  45.435, "city"),
    "Sinjar":               ("IQ", 36.319,  41.869, "city"),
    "Sadr City":            ("IQ", 33.374,  44.422, "district"),
    "Dohuk":                ("IQ", 36.868,  42.983, "city"),
    "Samarra":              ("IQ", 34.198,  43.872, "city"),
    "Baquba":               ("IQ", 33.745,  44.639, "city"),
    "Nasiriyah":            ("IQ", 31.046,  46.254, "city"),
    "Amarah":               ("IQ", 31.834,  47.151, "city"),
    "Kut":                  ("IQ", 32.496,  45.823, "city"),
    "Diwaniyah":            ("IQ", 31.991,  44.924, "city"),
    "Hillah":               ("IQ", 32.474,  44.422, "city"),
    # Provinces / regions
    # Western Anbar / CENTCOM ISIS op hotspots
    "Rawa":                 ("IQ", 34.478,  41.906, "city"),
    "Haditha":              ("IQ", 34.131,  42.381, "city"),
    "Hit":                  ("IQ", 33.645,  42.827, "city"),
    "al-Qa'im":             ("IQ", 34.386,  41.074, "city"),
    "Al Qa'im":             ("IQ", 34.386,  41.074, "city"),
    "Qaim":                 ("IQ", 34.386,  41.074, "city"),
    "Tal Afar":             ("IQ", 36.378,  42.449, "city"),
    "Qayyarah":             ("IQ", 35.826,  43.124, "city"),
    "Makhmur":              ("IQ", 35.771,  43.591, "city"),
    "Tuz Khurmatu":         ("IQ", 34.881,  44.634, "city"),
    "Al Anbar":             ("IQ", 32.560,  41.890, "region"),
    "Salah al-Din":         ("IQ", 34.200,  43.700, "region"),
    "Salah ad-Din":         ("IQ", 34.200,  43.700, "region"),
    "Anbar":                ("IQ", 32.560,  41.890, "region"),
    "Nineveh":              ("IQ", 36.370,  42.430, "region"),
    "Diyala":               ("IQ", 33.774,  45.150, "region"),
    "Babil":                ("IQ", 32.480,  44.500, "region"),
    "Iraqi Kurdistan":      ("IQ", 36.500,  44.500, "region"),
    "Kurdistan Region":     ("IQ", 36.500,  44.500, "region"),
    "southern Iraq":        ("IQ", 31.000,  46.000, "region"),
    "northern Iraq":        ("IQ", 36.000,  43.000, "region"),
    "western Iraq":         ("IQ", 33.000,  41.000, "region"),
    "Iraq":                 ("IQ", 33.223,  43.679, "country"),

    # ── Yemen ─────────────────────────────────────────────────────────────────
    "Sanaa airport":        ("YE", 15.477,  44.220, "site"),
    "Sanaa":                ("YE", 15.369,  44.191, "city"),
    "Sana'a":               ("YE", 15.369,  44.191, "city"),
    "Hodeidah":             ("YE", 14.798,  42.955, "city"),
    "Hudaydah":             ("YE", 14.798,  42.955, "city"),
    "Aden":                 ("YE", 12.779,  45.036, "city"),
    "Marib":                ("YE", 15.463,  45.322, "city"),
    "Taiz":                 ("YE", 13.577,  44.018, "city"),
    "Mukalla":              ("YE", 14.542,  49.130, "city"),
    "Saada":                ("YE", 16.936,  43.761, "city"),
    "Yemen":                ("YE", 15.552,  48.516, "country"),

    # ── Saudi Arabia ──────────────────────────────────────────────────────────
    "Riyadh":               ("SA", 24.688,  46.722, "city"),
    "Jeddah":               ("SA", 21.543,  39.173, "city"),
    "Mecca":                ("SA", 21.389,  39.857, "city"),
    "Medina":               ("SA", 24.468,  39.614, "city"),
    "Dhahran":              ("SA", 26.289,  50.152, "city"),
    "Abha":                 ("SA", 18.247,  42.505, "city"),
    "Jizan":                ("SA", 16.889,  42.551, "city"),
    "Saudi Arabia":         ("SA", 23.886,  45.079, "country"),

    # ── Jordan ────────────────────────────────────────────────────────────────
    "Amman":                ("JO", 31.956,  35.945, "city"),
    "Zarqa":                ("JO", 32.072,  36.088, "city"),
    "Irbid":                ("JO", 32.557,  35.855, "city"),
    "Aqaba":                ("JO", 29.526,  35.007, "city"),
    "Jordan":               ("JO", 30.586,  36.238, "country"),

    # ── Egypt ─────────────────────────────────────────────────────────────────
    "Rafah (Egypt)":        ("EG", 31.283,  34.226, "city"),
    "Cairo":                ("EG", 30.044,  31.236, "city"),
    "Alexandria":           ("EG", 31.200,  29.919, "city"),
    "Sinai":                ("EG", 30.425,  33.566, "region"),
    "North Sinai":          ("EG", 31.100,  33.800, "region"),
    "Suez Canal":           ("EG", 30.420,  32.330, "site"),
    "Port Said":            ("EG", 31.256,  32.284, "city"),
    "Suez":                 ("EG", 29.967,  32.550, "city"),
    "Arish":                ("EG", 31.130,  33.800, "city"),
    "Egypt":                ("EG", 26.820,  30.802, "country"),

    # ── Turkey ────────────────────────────────────────────────────────────────
    "Ankara":               ("TR", 39.920,  32.854, "city"),
    "Istanbul":             ("TR", 41.015,  28.979, "city"),
    "Incirlik":             ("TR", 37.002,  35.426, "site"),
    "Turkey":               ("TR", 38.964,  35.243, "country"),
    "Turkiye":              ("TR", 38.964,  35.243, "country"),

    # ── UAE / Gulf states ─────────────────────────────────────────────────────
    "Dubai":                ("AE", 25.197,  55.274, "city"),
    "Abu Dhabi":            ("AE", 24.453,  54.377, "city"),
    "Al Dhafra":            ("AE", 24.248,  54.547, "site"),   # USAF base Abu Dhabi
    "UAE":                  ("AE", 24.000,  54.000, "country"),
    "Al-Udeid":             ("QA", 25.117,  51.315, "site"),   # major USAF base
    "Al Udeid":             ("QA", 25.117,  51.315, "site"),
    "Doha":                 ("QA", 25.286,  51.533, "city"),
    "Qatar":                ("QA", 25.356,  51.184, "country"),
    "Kuwait City":          ("KW", 29.368,  47.978, "city"),
    "Camp Arifjan":         ("KW", 29.106,  48.020, "site"),   # US Army Kuwait
    "Ali Al Salem":         ("KW", 29.347,  47.521, "site"),   # USAF Kuwait
    "Kuwait":               ("KW", 29.368,  47.978, "country"),
    "Manama":               ("BH", 26.225,  50.586, "city"),
    "NSA Bahrain":          ("BH", 26.225,  50.586, "site"),   # US Naval base
    "Bahrain":              ("BH", 26.067,  50.558, "country"),
    "Muscat":               ("OM", 23.614,  58.593, "city"),
    "Oman":                 ("OM", 21.513,  55.923, "country"),

    # ── Libya ─────────────────────────────────────────────────────────────────
    "Tripoli":              ("LY", 32.902,  13.180, "city"),
    "Benghazi":             ("LY", 32.115,  20.069, "city"),
    "Libya":                ("LY", 26.336,  17.229, "country"),

    # ── Sudan ─────────────────────────────────────────────────────────────────
    "Khartoum":             ("SD", 15.501,  32.560, "city"),
    "Darfur":               ("SD", 13.500,  25.000, "region"),
    "Sudan":                ("SD", 12.863,  30.218, "country"),

    # ── Maritime / Straits ────────────────────────────────────────────────────
    "Bab al-Mandab":        ("YE", 12.583,  43.417, "water"),
    "Strait of Hormuz":     ("IR", 26.593,  56.459, "water"),
    "Hormuz":               ("IR", 26.593,  56.459, "water"),
    "Persian Gulf":         ("IR", 27.000,  51.000, "water"),
    "Gulf of Oman":         ("OM", 23.500,  58.500, "water"),
    "Gulf of Aden":         ("YE", 12.000,  47.000, "water"),
    "Red Sea":              ("YE", 20.000,  38.000, "water"),
    "Arabian Sea":          ("YE", 15.000,  65.000, "water"),
    "Gulf of Suez":         ("EG", 29.500,  32.700, "water"),
    "Mediterranean":        ("IL", 33.000,  28.000, "water"),

    # ── Actor / proxy terms (resolve to their primary operating zone) ─────────
    # These catch headlines that name an actor without a city
    "Hezbollah":            ("LB", 33.400,  35.500, "region"),
    "Houthi":               ("YE", 15.369,  44.191, "region"),
    "Houthis":              ("YE", 15.369,  44.191, "region"),
    "Ansarallah":           ("YE", 15.369,  44.191, "region"),
    "Hamas":                ("PS", 31.417,  34.313, "region"),
    "Islamic Jihad":        ("PS", 31.417,  34.313, "region"),
    "IRGC":                 ("IR", 35.694,  51.421, "region"),
    "Quds Force":           ("IR", 35.730,  51.300, "region"),
    "PMF":                  ("IQ", 33.340,  44.400, "region"),
    "Popular Mobilization": ("IQ", 33.340,  44.400, "region"),
    "PKK":                  ("IQ", 36.500,  44.500, "region"),

    # ── Border / frontier terms ───────────────────────────────────────────────
    "Lebanese border":      ("LB", 33.272,  35.203, "region"),
    "Syrian border":        ("SY", 33.500,  36.000, "region"),
    "Iraqi border":         ("IQ", 33.223,  43.679, "region"),
    "Iranian border":       ("IR", 35.000,  46.000, "region"),
    "Gaza border":          ("PS", 31.287,  34.245, "region"),
    "Israel-Lebanon border":("LB", 33.100,  35.400, "region"),
    "Israel-Gaza border":   ("PS", 31.320,  34.280, "region"),
}

# Specificity ranking — higher wins over lower
SPEC_RANK = {"site": 6, "crossing": 5, "district": 4, "city": 3, "region": 2, "water": 2, "country": 1}

# Sorted by name length descending so "Gaza City" matches before "Gaza"
GAZETTEER_SORTED = sorted(GAZETTEER.items(), key=lambda x: -len(x[0]))

# ── Event type classification ─────────────────────────────────────────────────
# (pattern, type, label, priority)
TYPE_RULES = [
    # High-specificity military first
    (r'\b(airstrike|air strike|air raid|bombed|bombing|bombs?|struck|strike|shelling|shelled)\b',
     'airstrike',  'Airstrike',       10),
    (r'\b(missile|rocket|ballistic|projectile|fired|launch(?:ed)?)\b',
     'missile',    'Missile/Rocket',   9),
    (r'\b(drone|UAV|unmanned)\b',
     'drone',      'Drone Strike',     9),
    (r'\b(naval|warship|destroyer|frigate|coast guard|maritime|tanker attacked|vessel)\b',
     'naval',      'Naval Incident',   9),
    (r'\b(nuclear|uranium|enrichment|centrifuge|IAEA|atomic|radioactive)\b',
     'nuclear',    'Nuclear Activity', 9),
    (r'\b(ground invasion|troops entered|soldiers cross|armored|tanks?|infantry|cross-border ground|ground operation|ground offensive)\b',
     'ground',     'Ground Operation', 9),
    (r'\b(kill(?:ed)?|dead|death|casualties|martyr|massacre|slaughter|execut)\b',
     'violence',   'Casualties',       8),
    (r'\b(terror|terrorist|attack(?:ed)?|assassinat|bomb(?:ing)?|explosion|blast)\b',
     'violence',   'Attack',           8),
    (r'\b(arrested|detained|captured|hostage|kidnap|abduct)\b',
     'arrest',     'Detention/Arrest', 7),
    (r'\b(protest|demonstrat|rally|march(?:ed)?|gather(?:ed)?)\b',
     'protest',    'Protest',          7),
    (r'\b(riot|clash(?:ed)?|unrest|violence)\b',
     'riot',       'Civil Unrest',     7),
    (r'\b(blockade|siege|embargo|sanctions?)\b',
     'logistics',  'Blockade/Sanctions',6),
    (r'\b(ceasefire|truce|negotiat|peace talks?|deal|agreement|accord)\b',
     'strategic',  'Diplomatic',       5),
    (r'\b(offensive|operation|military|forces?|troops?|IDF|Hamas|Hezbollah|IRGC|Houthi)\b',
     'conflict',   'Military Activity',4),
]

COMPILED_RULES = [(re.compile(pat, re.IGNORECASE), typ, lbl, pri)
                  for pat, typ, lbl, pri in TYPE_RULES]

# ── Category → type hints from RSS tags ──────────────────────────────────────
CATEGORY_HINTS = {
    "war & conflict":   ("conflict",  "Armed Conflict", 6),
    "conflict":         ("conflict",  "Armed Conflict", 6),
    "military":         ("conflict",  "Military",       5),
    "protests":         ("protest",   "Protest",        6),
    "diplomacy":        ("strategic", "Diplomatic",     5),
    "nuclear":          ("nuclear",   "Nuclear",        7),
    "drone":            ("drone",     "Drone",          7),
    "missile":          ("missile",   "Missile",        7),
    "hamas":            ("conflict",  "Hamas",          6),
    "hezbollah":        ("conflict",  "Hezbollah",      6),
    "houthis":          ("conflict",  "Houthi",         6),
    "israel":           ("conflict",  "Israel",         4),
    "iran":             ("strategic", "Iran",           4),
    "gaza":             ("conflict",  "Gaza",           5),
}

def classify(title, desc, categories):
    text = f"{title} {desc}"
    best_type, best_label, best_pri = "conflict", "News", 0

    # RSS category hints first (authoritative)
    for cat in categories:
        hint = CATEGORY_HINTS.get(cat.lower().strip())
        if hint and hint[2] > best_pri:
            best_type, best_label, best_pri = hint

    # Keyword rules on text (can override category if higher priority)
    for regex, typ, lbl, pri in COMPILED_RULES:
        if pri > best_pri and regex.search(text):
            best_type, best_label, best_pri = typ, lbl, pri

    return best_type, best_label

# ME bounding box for spaCy NER fallback: lat 10-43, lng 24-66
_ME_LAT  = (10.0, 43.0)
_ME_LNG  = (24.0, 66.0)

def _gazetteer_lookup(title, desc, categories):
    """
    Original gazetteer scan — exact word-boundary match with scoring.
    Returns (place, country, lat, lng) or None.
    """
    fields = [
        (title,                    3.0),
        (desc,                     1.0),
        (" ".join(categories),     1.5),
    ]
    best = None
    for place, (country, lat, lng, ptype) in GAZETTEER_SORTED:
        pattern = re.compile(r'\b' + re.escape(place) + r'\b', re.IGNORECASE)
        spec    = SPEC_RANK.get(ptype, 1)
        for text, field_w in fields:
            if not text:
                continue
            m = pattern.search(text)
            if not m:
                continue
            pos_w = 1.0 - 0.5 * (m.start() / max(len(text), 1))
            score = spec * field_w * pos_w
            if best is None or score > best[0]:
                best = (score, place, country, lat, lng)
    if best:
        return best[1], best[2], best[3], best[4]
    return None

def _spacy_geo_fallback(title, desc):
    """
    Use spaCy NER to extract GPE/LOC entities, look them up in the gazetteer
    by fuzzy name match, then filter to ME bounding box.
    Falls back to country-level centroid for known ME countries.
    """
    nlp = _get_nlp()
    if not nlp:
        return None

    text = f"{title} {desc}"
    doc  = nlp(text[:512])  # cap for speed

    # Collect unique GPE/LOC/FAC entities, title-case normalised
    candidates = []
    for ent in doc.ents:
        if ent.label_ in ("GPE", "LOC", "FAC"):
            candidates.append(ent.text.strip())

    if not candidates:
        return None

    # Score each candidate against gazetteer (case-insensitive substring + exact)
    best = None
    for cand in candidates:
        cand_l = cand.lower()
        for place, (country, lat, lng, ptype) in GAZETTEER_SORTED:
            if place.lower() == cand_l or cand_l in place.lower() or place.lower() in cand_l:
                spec  = SPEC_RANK.get(ptype, 1)
                score = spec * (2.0 if place.lower() == cand_l else 1.0)
                if best is None or score > best[0]:
                    best = (score, place, country, lat, lng)

    if best:
        _, place, country, lat, lng = best
        # Validate it falls within ME bounding box
        if _ME_LAT[0] <= lat <= _ME_LAT[1] and _ME_LNG[0] <= lng <= _ME_LNG[1]:
            return place, country, lat, lng

    return None

def extract_location(title, desc, categories):
    """
    Two-stage location extraction:
    1. Gazetteer exact match (fast, high precision)
    2. spaCy NER fallback (catches place names not in gazetteer)
    Returns (place_name, country_iso, lat, lng) or None.
    """
    result = _gazetteer_lookup(title, desc, categories)
    if result:
        return result
    # Gazetteer missed — try spaCy NER
    return _spacy_geo_fallback(title, desc)

# Severity keyword tiers — (keywords, base_score)
_SEV_CRITICAL_KW = {
    "dozens killed","hundreds killed","mass casualt","massacre","major offensive",
    "heavy bombardment","widespread destruction","multiple strikes","several strikes",
    "assassinat","broad wave of strikes","eliminated the commander","eliminated senior",
    "neutralized","direct hit on","struck and destroyed","large-scale strikes",
    "hit the carrier","struck the carrier","hypersonic","thermobaric",
    "chemical weapon","biological weapon","nuclear strike",
}
_SEV_HIGH_KW = {
    "killed","dead","deaths","casualt","wounded","injured","destroyed","degraded",
    "eliminated","airstrike","air strike","drone strike","precision strike",
    "ballistic missile","cruise missile","drone swarm","rocket fire",
    "anti-tank","warship","vessel seized","intercepted","seized",
    "idf forces","troops entered","resistance forces","islamic resistance",
    "retaliation","retaliatory","forces struck","ground offensive",
    "martyred","martyrdom","suppressed uprising","crackdown",
}
_SEV_MEDIUM_KW = {
    "attack","clash","clashes","fire","launched","arrest","detained","targeted",
    "damaged","disrupted","sanctions","nuclear talks","negotiations","drills",
    "exercise","mobilized","deployed","warned","threat","tension","escalat",
    "exchange of fire","border incident","incursion","patrol",
}

def _check_negated(doc, keyword):
    """
    Return True if the keyword appears negated in the spaCy doc.
    e.g. "no strikes", "did not kill", "denied killing"
    """
    kw_lower = keyword.lower()
    for token in doc:
        if kw_lower in token.text.lower():
            # Direct negation child: "not killed"
            if any(c.dep_ in _NEG_DEPS for c in token.children):
                return True
            # Negated head: "did not kill"
            if token.head and any(c.dep_ in _NEG_DEPS for c in token.head.children):
                return True
    return False

def _has_hedging(doc):
    """
    Return True if the sentence contains hedging/attribution verbs
    indicating unconfirmed reports (drops one severity tier).
    """
    for token in doc:
        if token.lemma_.lower() in _HEDGE_VERBS:
            return True
    return False

def severity_from_text(title, desc, source=None):
    """
    Negation-aware, hedge-aware severity scoring.
    1. Scan for keyword tier matches in title+desc
    2. Use spaCy dep-parse to check if matched keywords are negated
    3. Apply hedge penalty (drops one tier) if attribution verbs present
    4. Apply source discount for known over-escalatory sources
    """
    combined = f"{title} {desc}"
    text_l   = combined.lower()

    nlp = _get_nlp()
    doc = nlp(combined[:512]) if nlp else None

    def kw_active(kw):
        """True if keyword present AND not negated."""
        if kw not in text_l:
            return False
        if doc and _check_negated(doc, kw):
            return False
        return True

    # Determine raw tier
    if any(kw_active(kw) for kw in _SEV_CRITICAL_KW):
        raw = "critical"
    elif any(kw_active(kw) for kw in _SEV_HIGH_KW):
        raw = "high"
    elif any(kw_active(kw) for kw in _SEV_MEDIUM_KW):
        raw = "medium"
    else:
        raw = "low"

    # Hedge penalty — "Iran claims it struck" → drop one tier
    hedged = doc and _has_hedging(doc)

    # Source discount — Iranian state sources use escalatory vocab as standard prose
    discounted = source in _SOURCE_DISCOUNT if source else False

    # Apply penalties (max one tier drop per factor, cap at two drops total)
    tier_order = ["low", "medium", "high", "critical"]
    idx = tier_order.index(raw)
    if hedged:
        idx = max(0, idx - 1)
    if discounted and idx > 1:   # only discount if high or above
        idx = max(0, idx - 1)

    return tier_order[idx]

# ── RSS fetcher ───────────────────────────────────────────────────────────────
NAMESPACES = {
    "media":   "http://search.yahoo.com/mrss/",
    "dc":      "http://purl.org/dc/elements/1.1/",
    "content": "http://purl.org/rss/1.0/modules/content/",
    "atom":    "http://www.w3.org/2005/Atom",
}

def strip_html(s):
    return re.sub(r"<[^>]+>", " ", s or "").strip()

def fetch_feed(feed):
    """Try each URL candidate in order, return items from first that succeeds."""
    urls = feed.get("urls") or [feed.get("url","")]
    is_gnews = feed.get("gnews", False)
    last_err = None
    for url in urls:
        try:
            req = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(req, timeout=20) as r:
                raw = r.read()
            # Validate it's actually XML/RSS before parsing
            if b'<rss' not in raw and b'<feed' not in raw and b'<?xml' not in raw:
                log.debug("  %s: %s returned non-XML", feed["name"], url)
                continue
            root  = ET.fromstring(raw)
            items = root.findall(".//item")
            if not items:
                log.debug("  %s: %s returned 0 items", feed["name"], url)
                continue
            results = []
            for item in items:
                def g(tag):
                    el = item.find(tag)
                    if el is None:
                        for prefix, ns in NAMESPACES.items():
                            el = item.find(f"{{{ns}}}{tag}")
                            if el is not None: break
                    return (el.text or "").strip() if el is not None else ""

                title = strip_html(g("title"))
                desc  = strip_html(g("description") or g("summary"))[:400]
                pub   = g("pubDate") or g("published") or g("updated")
                cats  = [strip_html(c.text or "") for c in item.findall("category")]
                thumb = ""
                mt = item.find(f"{{{NAMESPACES['media']}}}thumbnail")
                if mt is not None: thumb = mt.get("url","")

                if is_gnews:
                    # Google News RSS quirks:
                    # 1. <link> is an Atom-style empty element; URL is in .tail not .text
                    link_el = item.find("link")
                    if link_el is not None and link_el.tail:
                        link = link_el.tail.strip()
                    else:
                        # fallback to guid which is the google redirect URL
                        link = g("guid")
                    # 2. Strip trailing source attribution Google appends to titles
                    #    e.g. "Israel strikes Tehran - Reuters" or "Gaza ceasefire | AP"
                    #    Also handles "... > U.S. Central Command" CENTCOM suffix
                    title = re.sub(r'\s*[-–|]\s*(Reuters|AP News|AP|Associated Press)\s*$', '', title, flags=re.IGNORECASE).strip()
                    title = re.sub(r'\s*>\s*U\.S\. Central Command\s*$', '', title, flags=re.IGNORECASE).strip()

                    # 3. Source name: always use feed["name"] for gnews feeds.
                    source_name = feed["name"]
                    # 4. domain_filter: only applied on non-site: queries.
                    #    site: queries wrap links as news.google.com redirects,
                    #    so a domain check on the link will always fail falsely.
                    domain_filter = feed.get("domain_filter")
                    is_site_query = "site:" in url
                    if domain_filter and link and not is_site_query:
                        check_url = link + " " + (g("guid") or "")
                        if not any(d in check_url for d in domain_filter):
                            continue  # skip — article is from a different outlet
                else:
                    link = g("link") or g("guid")
                    source_name = feed["name"]

                if title and link:
                    results.append({
                        "title": title, "url": link.strip(), "desc": desc,
                        "pub": pub, "categories": cats, "thumb": thumb,
                        "source": source_name, "credibility": feed["credibility"],
                        "region": feed["region"],
                        "military": feed.get("military", False),
                    })
            log.info("  %s: %d items (via %s)", feed["name"], len(results), url)
            return results
        except Exception as e:
            last_err = e
            log.info("  %s candidate failed: %s", feed["name"], str(e)[:80])
            continue

    # All URLs failed
    if feed.get("optional"):
        log.info("  [optional] %s: all %d URLs failed — %s", feed["name"], len(urls), str(last_err)[:80])
    else:
        log.warning("Feed %s: all URLs failed. Last error: %s", feed["name"], last_err)
    return []


# ── Process article into event ────────────────────────────────────────────────
def process_article(a):
    loc = extract_location(a["title"], a["desc"], a["categories"])
    # Filter: skip articles with no ME location
    if not loc:
        return None
    place, country, lat, lng = loc
    ev_type, ev_label = classify(a["title"], a["desc"], a["categories"])
    sev = severity_from_text(a["title"], a["desc"], source=a.get("source"))

    # Parse publish time
    pub_iso = ""
    try:
        dt = parsedate_to_datetime(a["pub"])
        pub_iso = dt.astimezone(timezone.utc).isoformat()
    except Exception:
        pub_iso = datetime.now(timezone.utc).isoformat()

    uid = hashlib.md5(a["url"].encode()).hexdigest()[:12]
    return {
        "id":          uid,
        "title":       a["title"],
        "summary":     a["desc"][:200],
        "url":         a["url"],
        "source":      a["source"],
        "credibility": a["credibility"],
        "region":      a["region"],
        "thumb":       a.get("thumb",""),
        "categories":  a["categories"][:5],
        "pub":         pub_iso,
        "fetched":     datetime.now(timezone.utc).isoformat(),
        "type":        ev_type,
        "label":       ev_label,
        "location":    place,
        "country":     country,
        "lat":         lat,
        "lng":         lng,
        "severity":    sev,
        "military":    a.get("military", False),
    }

# ── Seen URL cache ────────────────────────────────────────────────────────────
def load_seen():
    try:
        return set(json.loads(SEEN_FILE.read_text()))
    except Exception:
        return set()

def save_seen(seen):
    SEEN_FILE.write_text(json.dumps(list(seen)[-3000:]))

def load_existing():
    try:
        return json.loads(LATEST_FILE.read_text())
    except Exception:
        return []

# ── ISW / CriticalThreats fetcher ─────────────────────────────────────────────
ISW_BASE    = "https://www.criticalthreats.org/analysis"
ISW_SOURCE  = "ISW"
ISW_CRED    = 5

# Month names for slug construction
_MONTHS = ["january","february","march","april","may","june",
           "july","august","september","october","november","december"]

def _isw_slugs(date):
    """Return candidate URL slugs for a given date (datetime.date)."""
    m = _MONTHS[date.month - 1]
    d = date.day
    y = date.year
    base  = f"iran-update-{m}-{d}-{y}"
    morn  = f"iran-update-morning-special-report-{m}-{d}-{y}"
    eve   = f"iran-update-evening-special-report-{m}-{d}-{y}"
    # Return evening first (most comprehensive), then morning, then standard
    return [
        (eve,  "evening"),
        (morn, "morning"),
        (base, "standard"),
    ]


class _ISWParser(HTMLParser):
    """
    Minimal HTML parser that extracts:
      - Key Takeaways bullet items
      - Topline bold sentences + following body paragraph
    from a CriticalThreats article page.
    """
    def __init__(self):
        super().__init__()
        # Raw text extraction
        self._buf        = []      # current text accumulator
        self._in_main    = False   # inside main content div
        self._depth      = 0       # tag depth tracker for main div
        self._main_depth = 0

        # Structured extraction state
        self._in_strong  = False
        self._in_li      = False
        self._strong_buf = []
        self._li_buf     = []

        # Output
        self.takeaways   = []      # list of str
        self.toplines    = []      # list of {bold, body}
        self._cur_bold   = None    # active bold sentence being built
        self._cur_body   = []      # body lines after a bold

        # Section markers
        self._past_takeaways  = False
        self._in_takeaway_ul  = False
        self._past_toplines   = False

    # ── tag open ──────────────────────────────────────────────────────────────
    def handle_starttag(self, tag, attrs):
        attr_d = dict(attrs)
        cls    = attr_d.get("class","")

        # Detect main content area: first <article> or <div class*="content">
        if not self._in_main and tag in ("article","main"):
            self._in_main    = True
            self._main_depth = self._depth
        if not self._in_main and tag == "div" and (
                "content" in cls or "post-content" in cls or "entry" in cls):
            self._in_main    = True
            self._main_depth = self._depth

        if self._in_main:
            self._depth += 1

        if tag == "strong" or tag == "b":
            self._in_strong = True
            self._strong_buf = []

        if tag == "li" and self._in_takeaway_ul:
            self._in_li  = True
            self._li_buf = []

        # New paragraph closes any pending body accumulation
        if tag == "p" and self._cur_bold and self._cur_body:
            self._flush_topline()

    # ── tag close ─────────────────────────────────────────────────────────────
    def handle_endtag(self, tag):
        if self._in_main:
            self._depth -= 1
            if self._depth <= self._main_depth:
                self._in_main = False

        if tag in ("strong","b") and self._in_strong:
            self._in_strong = False
            text = _clean(" ".join(self._strong_buf))
            if not text:
                return

            # Detect section markers
            lower = text.lower()
            if "key takeaway" in lower:
                self._past_takeaways = True
                self._in_takeaway_ul = True
                return
            if "topline" in lower or "key development" in lower:
                self._past_toplines  = True
                self._in_takeaway_ul = False
                return

            # A bold sentence in the toplines section becomes a topline
            if self._past_toplines and len(text) > 30:
                if self._cur_bold:
                    self._flush_topline()
                self._cur_bold  = text
                self._cur_body  = []

        if tag == "li" and self._in_li:
            self._in_li = False
            text = _clean(" ".join(self._li_buf))
            if text and self._past_takeaways and len(text) > 20:
                self.takeaways.append(text)
                # After first real takeaway, no longer need to track the UL
                self._in_takeaway_ul = True

        if tag == "ul":
            self._in_takeaway_ul = False

        if tag in ("article","main","div") and self._cur_bold and self._cur_body:
            self._flush_topline()

    # ── text ──────────────────────────────────────────────────────────────────
    def handle_data(self, data):
        data = data.strip()
        if not data:
            return
        if self._in_strong:
            self._strong_buf.append(data)
        elif self._in_li:
            self._li_buf.append(data)
        elif self._cur_bold and self._past_toplines:
            self._cur_body.append(data)

    # ── helpers ───────────────────────────────────────────────────────────────
    def _flush_topline(self):
        body = _clean(" ".join(self._cur_body))
        self.toplines.append({"bold": self._cur_bold, "body": body})
        self._cur_bold = None
        self._cur_body = []


def _clean(text):
    """Strip footnote refs [[i]], [[ii]], excess whitespace."""
    text = re.sub(r'\[\[.*?\]\]', '', text)   # footnote refs
    text = re.sub(r'\[.*?\]',     '', text)   # any remaining brackets
    text = re.sub(r'\s+',         ' ', text)
    return text.strip()


def _parse_isw_date_from_slug(slug):
    """Extract ISO date string from a slug like iran-update-evening-special-report-march-4-2026."""
    m = re.search(r'(' + '|'.join(_MONTHS) + r')-(\d{1,2})-(\d{4})', slug)
    if not m:
        return datetime.now(timezone.utc).isoformat()
    month_num = _MONTHS.index(m.group(1)) + 1
    return datetime(int(m.group(3)), month_num, int(m.group(2)),
                    12, 0, 0, tzinfo=timezone.utc).isoformat()


def fetch_isw_page(url):
    """Fetch a CriticalThreats page, return raw HTML string or None."""
    try:
        req = urllib.request.Request(url, headers={
            **HEADERS,
            "Accept": "text/html,application/xhtml+xml",
        })
        with urllib.request.urlopen(req, timeout=20) as r:
            if r.status != 200:
                return None
            raw = r.read()
            # Detect encoding
            enc = "utf-8"
            ct  = r.headers.get("Content-Type","")
            m   = re.search(r'charset=([\w-]+)', ct)
            if m: enc = m.group(1)
            return raw.decode(enc, errors="replace")
    except Exception as e:
        log.debug("ISW fetch %s: %s", url, e)
        return None


def parse_isw_html(html, url, slug, edition, date_iso):
    """
    Parse fetched HTML into a list of event dicts — one per takeaway/topline.
    Returns [] if the page looks like a 404 / redirect.
    """
    # Quick sanity: page must mention "Iran Update" or "ISW"
    if "Iran Update" not in html and "ISW" not in html:
        return []

    parser = _ISWParser()
    try:
        parser.feed(html)
    except Exception as e:
        log.debug("ISW parse error %s: %s", url, e)

    events = []

    # ── Key Takeaways → assessment cards ──────────────────────────────────────
    for i, txt in enumerate(parser.takeaways[:8]):
        loc = extract_location(txt, "", [])
        if not loc:
            continue
        place, country, lat, lng = loc
        ev_type, ev_label = classify(txt, "", [])
        sev = severity_from_text(txt, "")
        uid = hashlib.md5(f"{url}:takeaway:{i}".encode()).hexdigest()[:12]
        events.append({
            "id":           uid,
            "title":        txt[:200],
            "summary":      txt[:400],
            "url":          url,
            "source":       ISW_SOURCE,
            "credibility":  ISW_CRED,
            "region":       "ME",
            "categories":   ["ISW", edition],
            "pub":          date_iso,
            "fetched":      datetime.now(timezone.utc).isoformat(),
            "type":         ev_type,
            "label":        ev_label,
            "location":     place,
            "country":      country,
            "lat":          lat,
            "lng":          lng,
            "severity":     sev,
            "isw_edition":  edition,
            "isw_section":  "takeaway",
        })

    # ── Topline assessments → event cards ─────────────────────────────────────
    for i, item in enumerate(parser.toplines[:15]):
        bold = item["bold"]
        body = item["body"]
        # Use bold as title, body as summary
        loc = extract_location(bold, body, [])
        if not loc:
            # Try bold-only fallback before skipping
            loc = extract_location(bold, "", [])
        if not loc:
            continue
        place, country, lat, lng = loc
        ev_type, ev_label = classify(bold, body, [])
        sev = severity_from_text(bold, body)
        uid = hashlib.md5(f"{url}:topline:{i}".encode()).hexdigest()[:12]
        events.append({
            "id":           uid,
            "title":        bold[:200],
            "summary":      body[:400],
            "url":          url,
            "source":       ISW_SOURCE,
            "credibility":  ISW_CRED,
            "region":       "ME",
            "categories":   ["ISW", edition],
            "pub":          date_iso,
            "fetched":      datetime.now(timezone.utc).isoformat(),
            "type":         ev_type,
            "label":        ev_label,
            "location":     place,
            "country":      country,
            "lat":          lat,
            "lng":          lng,
            "severity":     sev,
            "isw_edition":  edition,
            "isw_section":  "topline",
        })

    log.info("  ISW %s: %d takeaways, %d toplines → %d events",
             slug, len(parser.takeaways), len(parser.toplines), len(events))
    return events


def fetch_isw():
    """
    Try URL candidates for today and the previous RETAIN_DAYS-1 days.
    Returns flat list of ISW event dicts.
    """
    today = datetime.now(timezone.utc).date()
    dates = [today - timedelta(days=i) for i in range(RETAIN_DAYS)]

    # Load existing ISW events to avoid re-fetching same slugs
    try:
        existing_isw = json.loads(ISW_FILE.read_text())
    except Exception:
        existing_isw = []
    seen_urls = {e["url"] for e in existing_isw}

    all_events = []
    fetched_urls = set()

    for date in dates:
        date_new_events = []
        for slug, edition in _isw_slugs(date):
            url = f"{ISW_BASE}/{slug}"
            if url in seen_urls or url in fetched_urls:
                log.debug("ISW skip (seen): %s", slug)
                continue
            fetched_urls.add(url)
            html = fetch_isw_page(url)
            if not html:
                log.debug("ISW not found: %s", slug)
                continue
            date_iso = _parse_isw_date_from_slug(slug)
            events   = parse_isw_html(html, url, slug, edition, date_iso)
            if events:
                date_new_events.extend(events)
                log.info("ISW ✓ %s → %d events", slug, len(events))
        all_events.extend(date_new_events)

    if not all_events and existing_isw:
        log.info("ISW: no new updates found, keeping %d existing", len(existing_isw))
        return existing_isw

    # Merge: new events first, then existing not already present
    merged_ids = {e["id"] for e in all_events}
    for e in existing_isw:
        if e["id"] not in merged_ids:
            all_events.append(e)
            merged_ids.add(e["id"])

    all_events.sort(key=lambda e: e.get("pub",""), reverse=True)
    # Drop ISW events older than RETAIN_DAYS
    cutoff_isw = (datetime.now(timezone.utc) - timedelta(days=RETAIN_DAYS)).isoformat()
    all_events = [e for e in all_events if e.get("pub","") >= cutoff_isw]

    ISW_FILE.write_text(json.dumps(all_events, separators=(",",":")))
    return all_events



# ── Poll cycle ────────────────────────────────────────────────────────────────

def poll_cycle():
    log.info("─── Fetching RSS feeds ───")
    seen     = load_seen()
    existing = load_existing()

    all_raw = []
    for feed in FEEDS:
        all_raw.extend(fetch_feed(feed))

    new_raw = [a for a in all_raw if a["url"] not in seen]
    log.info("New articles: %d / %d total | %d new",
             len(all_raw), len(all_raw), len(new_raw))

    # Per-source breakdown
    from collections import Counter
    src_counts = Counter(a["source"] for a in all_raw)
    src_new    = Counter(a["source"] for a in new_raw)
    for src, total in sorted(src_counts.items()):
        log.info("  %-20s total=%-4d  new=%d", src, total, src_new.get(src, 0))

    new_events = []
    geo_misses = Counter()  # track which sources lose items to gazetteer
    for a in new_raw:
        seen.add(a["url"])
        ev = process_article(a)
        if ev:
            new_events.append(ev)
        else:
            geo_misses[a["source"]] += 1

    if geo_misses:
        log.info("Gazetteer misses: %s", dict(geo_misses))

    # Per-source events produced
    ev_counts = Counter(e["source"] for e in new_events)
    log.info("ME-relevant events: %d  →  %s", len(new_events), dict(ev_counts))

    # Merge with existing, deduplicate by id, drop events older than RETAIN_DAYS
    cutoff = (datetime.now(timezone.utc) - timedelta(days=RETAIN_DAYS)).isoformat()
    seen_ids = set()
    merged = []
    for e in new_events + existing:
        if e["id"] in seen_ids:
            continue
        seen_ids.add(e["id"])
        if e.get("pub", "") >= cutoff:
            merged.append(e)
    merged.sort(key=lambda e: e.get("pub",""), reverse=True)

    LATEST_FILE.write_text(json.dumps(merged, separators=(",",":")))
    save_seen(seen)
    log.info("✓ latest.json: %d events across %d days (cutoff %s)",
             len(merged), RETAIN_DAYS, cutoff[:10])

    # ── ISW ───────────────────────────────────────────────────────────────────
    log.info("─── Fetching ISW ───")
    isw_events = fetch_isw()

    STATUS_FILE.write_text(json.dumps({
        "count":       len(merged),
        "new":         len(new_events),
        "isw_count":   len(isw_events),
        "fetched_at":  datetime.now(timezone.utc).isoformat(),
        "feeds":       [f["name"] for f in FEEDS] + ["ISW"],
    }, indent=2))
    save_seen(seen)
    log.info("✓ Done. RSS: %d events, ISW: %d assessments", len(merged), len(isw_events))

# ── HTTP Server ───────────────────────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args): pass

    def do_GET(self):
        path = self.path.lstrip("/").split("?")[0]
        if path == "status":             self.serve(STATUS_FILE)
        elif path in ("latest.json",""): self.serve(LATEST_FILE)
        elif path == "isw.json":         self.serve(ISW_FILE)
        elif path == "refresh":
            t = threading.Thread(target=poll_cycle, daemon=True)
            t.start()
            t.join()   # block until feeds are fully re-polled
            self.respond(200, b'{"status":"ok"}')
        else: self.respond(404, b'{"error":"not found"}')

    def do_OPTIONS(self):
        self.send_response(200); self.cors(); self.end_headers()

    def serve(self, fp):
        fp = Path(fp)
        if not fp.exists():
            self.respond(200, b'{"status":"waiting"}'); return
        data = fp.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type","application/json")
        self.send_header("Content-Length", str(len(data)))
        self.cors(); self.end_headers(); self.wfile.write(data)

    def respond(self, code, body):
        self.send_response(code)
        self.send_header("Content-Type","application/json")
        self.cors(); self.end_headers(); self.wfile.write(body)

    def send_error(self, code, message=None, explain=None):
        self.respond(code, json.dumps({"error":code,"message":message or ""}).encode())

    def cors(self):
        self.send_header("Access-Control-Allow-Origin","*")
        self.send_header("Access-Control-Allow-Methods","GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers","*")
        self.send_header("Cache-Control","no-cache")

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--reset-seen", action="store_true",
                    help="Clear seen-URL cache so all current feed items are reprocessed")
    args = ap.parse_args()

    DATA_DIR.mkdir(exist_ok=True)
    if args.reset_seen:
        if SEEN_FILE.exists():
            SEEN_FILE.unlink()
            log.info("Cleared seen-URL cache — all feed items will be reprocessed")
    # Initial fetch on startup
    threading.Thread(target=poll_cycle, daemon=True).start()
    server = HTTPServer(("localhost", PORT), Handler)
    log.info("Conflict Monitor RSS server → http://localhost:%d", PORT)
    log.info("  GET /latest.json  — all ME events")
    log.info("  GET /refresh      — manual refresh trigger")
    log.info("  GET /status       — feed status")
    required = [f["name"] for f in FEEDS if not f.get("optional")]
    optional = [f["name"] for f in FEEDS if f.get("optional")]
    log.info("  Feeds (required): %s", ", ".join(required))
    if optional:
        log.info("  Feeds (optional): %s", ", ".join(optional))
    log.info("  + ISW (CriticalThreats scraper)")
    try: server.serve_forever()
    except KeyboardInterrupt: log.info("Stopped.")

if __name__ == "__main__": main()
