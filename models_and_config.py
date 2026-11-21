"""유령 환승 필터링 라우터의 계약: 열거형, Pydantic 스키마, 설정, 상수, 기록 저장소 DDL.

로직은 두지 않는다(§3.3). 열거형, 스키마, 검증기, 파생 속성, 상수만 둔다.
모든 모델은 불변(frozen)이고 순서가 있는 묶음은 tuple 이다.
표준 라이브러리와 pydantic 만 임포트한다(§3.1).
"""

import datetime
import enum
import re
import statistics
from types import MappingProxyType
from typing import Annotated, Literal

from pydantic import BaseModel, ConfigDict, Field, StringConstraints, model_validator

# ===== 공통 자료형과 검증 도우미 =====

NonEmptyStr = Annotated[str, StringConstraints(min_length=1)]
PositiveFloat = Annotated[float, Field(gt=0)]
NonNegFloat = Annotated[float, Field(ge=0)]
NonNegInt = Annotated[int, Field(ge=0)]
Probability = Annotated[float, Field(ge=0, le=1)]
Latitude = Annotated[float, Field(ge=-90, le=90)]
Longitude = Annotated[float, Field(ge=-180, le=180)]
LatLon = tuple[float, float]

_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
_DATE_IN_TEXT_RE = re.compile(r"\d{4}-\d{2}-\d{2}")
_HHMM_RE = re.compile(r"^([01]\d|2[0-3]):[0-5]\d$")
_URL_FIELD_RE = re.compile(r"\{([A-Za-z_][A-Za-z0-9_]*)\}")

SECONDS_PER_DAY = 86_400.0
TWO_DAYS_S = 172_800.0


def _check_date(value: str, what: str) -> None:
    """YYYY-MM-DD 형식이고 실제로 있는 날짜인지 확인한다."""
    if not _DATE_RE.match(value):
        raise ValueError(f"{what} '{value}' 는 YYYY-MM-DD 형식이 아닙니다")
    try:
        datetime.date.fromisoformat(value)
    except ValueError as exc:
        raise ValueError(f"{what} '{value}' 는 없는 날짜입니다") from exc


def _check_hhmm(value: str, what: str) -> None:
    """HH:MM (00:00 ~ 23:59) 형식인지 확인한다."""
    if not _HHMM_RE.match(value):
        raise ValueError(f"{what} '{value}' 는 HH:MM 형식의 시각이 아닙니다")


def _hhmm_minutes(value: str) -> int:
    """검증된 HH:MM 문자열을 0시부터의 분으로 바꾼다."""
    hours, minutes = value.split(":")
    return int(hours) * 60 + int(minutes)


def _non_decreasing(values: tuple[float, ...]) -> bool:
    """줄어들지 않는 순서인지 본다."""
    return all(a <= b for a, b in zip(values, values[1:]))


def _duplicates(values: list[str] | tuple[str, ...]) -> list[str]:
    """두 번 이상 나온 값을 처음 나온 순서로 돌려준다."""
    seen: set[str] = set()
    dup: list[str] = []
    for value in values:
        if value in seen and value not in dup:
            dup.append(value)
        seen.add(value)
    return dup


class _Frozen(BaseModel):
    """모든 스키마의 바탕. 불변이고 정의하지 않은 필드는 받지 않는다."""

    model_config = ConfigDict(frozen=True, extra="forbid")


# ===== 열거형 (§3.3) =====


class NodeType(enum.StrEnum):
    PLACE = "PLACE"
    INTERSECTION = "INTERSECTION"
    WAYPOINT = "WAYPOINT"
    BUS_STOP = "BUS_STOP"
    SUBWAY_PLATFORM = "SUBWAY_PLATFORM"
    STATION_HALL = "STATION_HALL"
    STATION_EXIT = "STATION_EXIT"
    BIKE_STATION = "BIKE_STATION"
    POINT = "POINT"


class Mode(enum.StrEnum):
    """엣지의 통행 수단."""

    WALK = "WALK"
    BIKE = "BIKE"


class TravelMode(enum.StrEnum):
    """수단 토글과 탑승 수단. 도보는 항상 쓴다."""

    BUS = "BUS"
    SUBWAY = "SUBWAY"
    BIKE = "BIKE"


class EdgeKind(enum.StrEnum):
    SIDEWALK = "SIDEWALK"
    CROSSWALK = "CROSSWALK"
    ALLEY = "ALLEY"
    UNDERPASS = "UNDERPASS"
    OVERPASS = "OVERPASS"
    STAIRS = "STAIRS"
    BIKE_LANE = "BIKE_LANE"
    STATION_PASSAGE = "STATION_PASSAGE"
    SNAP = "SNAP"


class SignalState(enum.StrEnum):
    GREEN = "GREEN"
    RED = "RED"
    STOCHASTIC = "STOCHASTIC"


class SignalSource(enum.StrEnum):
    DESIGN = "DESIGN"
    LEARNED = "LEARNED"


class OriginKind(enum.StrEnum):
    AT_NODE = "AT_NODE"
    AT_POINT = "AT_POINT"
    ON_BUS = "ON_BUS"
    ON_TRAIN = "ON_TRAIN"


class BusRouteType(enum.StrEnum):
    TRUNK = "TRUNK"  # 간선
    BRANCH = "BRANCH"  # 지선
    CIRCULAR = "CIRCULAR"  # 순환
    WIDE_AREA = "WIDE_AREA"  # 광역
    NIGHT = "NIGHT"  # 심야
    VILLAGE = "VILLAGE"  # 마을


class PredictionKind(enum.StrEnum):
    """버스 예측 칸의 종류(§1.7.1, §5.2)."""

    NORMAL = "NORMAL"
    WAITING = "WAITING"
    ENDED = "ENDED"
    NO_INFO = "NO_INFO"


class TimeSource(enum.StrEnum):
    """차량 시각의 출처(§1.7)."""

    PREDICTED = "PREDICTED"
    EXTENDED = "EXTENDED"
    HEADWAY = "HEADWAY"
    TIMETABLE = "TIMETABLE"


class RunTimeSource(enum.StrEnum):
    """구간 운행시간의 출처(§1.7.1)."""

    PREDICTION = "PREDICTION"
    DESIGN = "DESIGN"


class SearchRun(enum.StrEnum):
    """탐색 실행 조건(§1.10.5). 정의 순서가 실행 순서다."""

    FULL = "FULL"
    NO_BIKE = "NO_BIKE"
    BUS_ONLY = "BUS_ONLY"
    SUBWAY_ONLY = "SUBWAY_ONLY"
    SLOW = "SLOW"
    AVERSE = "AVERSE"
    NAIVE = "NAIVE"


class WaitRule(enum.StrEnum):
    """탐색에서 표본 신호의 대기를 보는 규칙(§1.10.3)."""

    EXPECTED = "EXPECTED"
    WORST = "WORST"
    NONE = "NONE"


class RankCriterion(enum.StrEnum):
    MEAN_ARRIVAL = "MEAN_ARRIVAL"
    P90_ARRIVAL = "P90_ARRIVAL"
    ON_TIME = "ON_TIME"
    UTILITY = "UTILITY"


class FullVehiclePolicy(enum.StrEnum):
    IGNORE = "IGNORE"
    SKIP = "SKIP"


class NaiveTransferWait(enum.StrEnum):
    ZERO = "ZERO"
    REAL = "REAL"


class RouteStatus(enum.StrEnum):
    RANKED = "RANKED"
    GHOST_PRUNED = "GHOST_PRUNED"


class Grade(enum.StrEnum):
    SAFE = "SAFE"
    RISKY = "RISKY"
    GHOST = "GHOST"


class ReasonCode(enum.StrEnum):
    LAST_VEHICLE_RISK = "LAST_VEHICLE_RISK"
    LOW_PLAN_PROBABILITY = "LOW_PLAN_PROBABILITY"
    UNREACHABLE = "UNREACHABLE"


class ProbMethod(enum.StrEnum):
    EXACT = "EXACT"
    QMC = "QMC"
    DEGENERATE = "DEGENERATE"


class LegKind(enum.StrEnum):
    """화면의 시간 막대 칸."""

    WALK = "WALK"
    SIGNAL_WAIT = "SIGNAL_WAIT"
    BIKE_UNLOCK = "BIKE_UNLOCK"
    BIKE = "BIKE"
    BIKE_DOCK = "BIKE_DOCK"
    STOP_WAIT = "STOP_WAIT"
    BUS = "BUS"
    SUBWAY = "SUBWAY"


class StationUse(enum.StrEnum):
    """대여소 상태(§1.3). 고른 여정의 대여·반납 표시는 화면이 덧붙인다(§6.5)."""

    AVAILABLE = "AVAILABLE"
    NO_BIKE = "NO_BIKE"
    LOW_P_BIKE = "LOW_P_BIKE"


class EngineStatus(enum.StrEnum):
    OK = "OK"
    NO_ROUTE = "NO_ROUTE"
    SNAP_FAILED = "SNAP_FAILED"


class DataMode(enum.StrEnum):
    SIMULATION = "SIMULATION"
    REPLAY = "REPLAY"
    LIVE = "LIVE"


class DayType(enum.StrEnum):
    WEEKDAY = "WEEKDAY"
    SATURDAY = "SATURDAY"
    HOLIDAY = "HOLIDAY"


class WarningCode(enum.StrEnum):
    """경고 코드(§3.5 의 표)."""

    NO_ROUTE = "NO_ROUTE"
    SNAP_FAILED = "SNAP_FAILED"
    NO_VEHICLE_TIMES = "NO_VEHICLE_TIMES"
    PREDICTION_NOT_MONOTONE = "PREDICTION_NOT_MONOTONE"
    PREDICTION_OVERTAKE = "PREDICTION_OVERTAKE"
    NO_HEADWAY = "NO_HEADWAY"
    STALE_PREDICTION = "STALE_PREDICTION"
    TIMETABLE_OVERTAKE = "TIMETABLE_OVERTAKE"
    TIMETABLE_STATION_UNUSED = "TIMETABLE_STATION_UNUSED"
    UNVERIFIED_DISTANCE = "UNVERIFIED_DISTANCE"
    SIGNAL_DATA_INCONSISTENT = "SIGNAL_DATA_INCONSISTENT"
    TRANSFER_WINDOW_EXCEEDED = "TRANSFER_WINDOW_EXCEEDED"
    CLIMATE_CARD_NOT_APPLICABLE = "CLIMATE_CARD_NOT_APPLICABLE"
    UNVERIFIED_COORDINATES = "UNVERIFIED_COORDINATES"
    QMC_DIMENSIONS_CAPPED = "QMC_DIMENSIONS_CAPPED"
    DEADLINE_MISSING = "DEADLINE_MISSING"
    LIVE_DATA_SKIPPED = "LIVE_DATA_SKIPPED"
    LIVE_DATA_FAILED = "LIVE_DATA_FAILED"
    DAYTYPE_NOT_LEARNED = "DAYTYPE_NOT_LEARNED"
    REPLAY_DATA_GAP = "REPLAY_DATA_GAP"


class SourceKind(enum.StrEnum):
    """원천 상태의 원천. 정의 순서가 `ApiSourceStatus` 를 늘어놓는 순서다(§3.3)."""

    BUS_ARRIVAL = "BUS_ARRIVAL"
    BIKE = "BIKE"
    SIGNAL = "SIGNAL"
    SUBWAY_TIMETABLE = "SUBWAY_TIMETABLE"


class SourceState(enum.StrEnum):
    SUCCESS = "SUCCESS"
    FAILED = "FAILED"
    SKIPPED = "SKIPPED"


# ===== 공통 상수 =====

# 요일 종류의 순서(시각표, 학습값, 화면 표시).
DAY_TYPE_ORDER: tuple[DayType, ...] = (DayType.WEEKDAY, DayType.SATURDAY, DayType.HOLIDAY)

# 준난수 밑: 2 ~ 61 의 소수 18개(§1.4.4).
HALTON_PRIMES: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)

# 키를 읽는 환경변수 이름(§5.5). EngineConfig 의 기본값과 API_SPECS 가 함께 쓴다.
ENV_SEOUL_KEY = "SEOUL_OPENAPI_KEY"
ENV_DATA_GO_KR_KEY = "DATA_GO_KR_SERVICE_KEY"
ENV_KAKAO_KEY = "KAKAO_REST_API_KEY"
ENV_TDATA_KEY = "SEOUL_TDATA_API_KEY"  # 서울 t-data 신호 잔여시간(31단계)

# 화면에서 조절하는 값의 (최솟값, 최댓값, 간격). §0.3 의 "화면에서 조절" 열, §6.3 의 사이드바와 같다.
# EngineConfig 필드가 아닌 것: depart_offset_s (출발 늦추기, §4.6), prior_distance_km (이미 탄 거리, §6.3).
PARAM_RANGES: MappingProxyType = MappingProxyType(
    {
        "gamma": (1.05, 2.0, 0.05),
        "v_walk_mps": (0.8, 1.8, 0.05),
        "v_pm_mps": (2.5, 6.0, 0.1),
        "safety_buffer_s": (0.0, 120.0, 5.0),
        "w_time": (0.0, 1.0, 0.05),
        "w_cost": (0.0, 1.0, 0.05),
        "w_risk": (0.0, 1.0, 0.05),
        "max_rides": (1, 5, 1),
        "max_bike_legs": (0, 2, 1),
        "depart_offset_s": (0.0, 1800.0, 60.0),
        "prior_distance_km": (0.0, 60.0, 0.1),
    }
)

# 걷는 속도 프리셋 (m/s, §0.3). "보통"이 기본값이다.
WALK_SPEED_PRESETS: MappingProxyType = MappingProxyType({"느리게": 1.0, "보통": 1.25, "빠르게": 1.5})

# 종합 점수 가중치 프리셋 (w_time, w_cost, w_risk). "균형"이 기본값이다.
WEIGHT_PRESETS: MappingProxyType = MappingProxyType(
    {
        "균형": (0.5, 0.2, 0.3),
        "시간 우선": (0.7, 0.1, 0.2),
        "요금 우선": (0.3, 0.5, 0.2),
        "안전 우선": (0.3, 0.1, 0.6),
    }
)

# 버스 API 의 routeType 코드 → 노선 종류(§3.3). 심야버스는 노선 이름이 NIGHT_ROUTE_PREFIX 로 시작하면
# 코드보다 먼저 NIGHT 로 둔다. 그 밖의 코드(공항 1, 인천 7, 경기 8, 폐지 9, 공용 0)는 범위 밖이다(§4.9).
ROUTE_TYPE_CODES: MappingProxyType = MappingProxyType(
    {
        "2": BusRouteType.VILLAGE,
        "3": BusRouteType.TRUNK,
        "4": BusRouteType.BRANCH,
        "5": BusRouteType.CIRCULAR,
        "6": BusRouteType.WIDE_AREA,
    }
)
NIGHT_ROUTE_PREFIX = "N"

# FARE_NOTES 의 자리 표시 이름. S4 의 fare_notes(config) 가 설정값으로 채운다(§0.4).
FARE_NOTE_FIELDS: tuple[str, ...] = (
    "fare_subway_krw",
    "fare_bus_trunk_krw",
    "fare_bus_branch_krw",
    "fare_bus_circular_krw",
    "fare_bus_wide_area_krw",
    "fare_bus_night_krw",
    "fare_bus_village_krw",
    "fare_free_distance_km",
    "fare_step_km",
    "fare_step_krw",
    "fare_long_km",
    "fare_long_step_km",
    "max_rides_per_chain",
    "max_transfers",
    "bike_pass_krw",
    "bike_mileage_discount_krw",
    "transfer_window_min",
    "transfer_window_night_min",
    "night_from_hhmm",
    "night_to_hhmm",
)

# 요금 안내 문구(화면 ⑤ 탭, §1.5, §1.6). 금액과 시간은 숫자로 적지 않고 자리 표시로 둔다.
FARE_NOTES: tuple[str, ...] = (
    "요금 기준: 교통카드 일반(성인) 요금이며 2026-11-18 에 다시 확인했습니다. 출처는 서울시 교통요금표, "
    "서울시 통합환승 할인제도 안내, 서울시 미디어허브 기후동행패스 Q&A, 기후동행카드 단기권 안내입니다.",
    "기본요금: 지하철 {fare_subway_krw:,}원, 서울 시내버스 간선 {fare_bus_trunk_krw:,}원, "
    "지선 {fare_bus_branch_krw:,}원, 순환 {fare_bus_circular_krw:,}원, 광역 {fare_bus_wide_area_krw:,}원, "
    "심야 {fare_bus_night_krw:,}원, 마을버스 {fare_bus_village_krw:,}원입니다.",
    "갈아타면 탄 수단의 기본요금 가운데 가장 높은 값을 한 번 내고, 탄 거리의 합이 {fare_free_distance_km:g} km 를 "
    "넘으면 {fare_step_km:g} km 마다 {fare_step_krw:,}원을 더합니다(통합 거리비례). 더 비싼 수단으로 갈아탈 때 "
    "차액을 내는 실제 방식과 합계가 같습니다.",
    "서울 시내버스를 한 번만 타면 거리와 상관없이 기본요금입니다. 지하철만 타면 {fare_long_km:g} km 까지는 "
    "{fare_step_km:g} km 마다, 그 뒤로는 {fare_long_step_km:g} km 마다 {fare_step_krw:,}원을 더합니다.",
    "지하철끼리 개찰구 안에서 갈아타면 한 번 탄 것으로 계산합니다. 지하철에서 내려 역 밖으로 나온 뒤 다시 "
    "지하철을 타면 환승으로 보지 않고 기본요금을 새로 냅니다.",
    "환승 인정 시간은 내린 뒤 {transfer_window_min:g}분이고, 다음 승차가 {night_from_hhmm} ~ {night_to_hhmm} "
    "사이면 {transfer_window_night_min:g}분입니다. 환승은 {max_transfers}회(승차 {max_rides_per_chain}회)까지이고 "
    "같은 버스 노선을 다시 타는 것은 환승이 아닙니다. 이 시간을 넘기면 기본요금을 다시 냅니다.",
    "기후동행카드 30일권은 2026년 9월 30일(선불은 9월 29일)로 끝났습니다. '기후동행카드 단기권 보유'를 켜면 "
    "지하철과 서울 시내·마을버스 요금을 0원으로 계산합니다. 광역버스와 따릉이는 단기권에 들지 않아, 광역버스를 "
    "타는 여정에는 단기권을 적용하지 않고 따릉이 요금은 그대로 더합니다.",
    "후속 기후동행패스는 탈 때 정상 요금을 내고 한 달 교통비의 일부를 돌려받는 환급 방식이라 이 요금 계산에는 "
    "넣지 않습니다.",
    "따릉이를 빌리는 여정은 1시간권 {bike_pass_krw:,}원을 한 번 더합니다. 1시간권은 그날 여러 번 빌릴 수 있습니다.",
    "'따릉이 환승 마일리지 적용'은 {bike_mileage_discount_krw:,}원을 바로 빼는 가정입니다. 실제 제도는 정기권과 "
    "등록한 교통카드가 있을 때 대중교통에서 내린 뒤 정해진 시간 안에 빌리면 마일리지를 적립하는 방식이라 "
    "금액과 조건이 다릅니다.",
    "조조할인, 차등요금 지선버스(지선 기본요금으로 계산), 광역버스의 장거리 추가요금, 신분당선 별도 운임은 "
    "다루지 않습니다.",
)

# 기록 저장소의 표 정의 (§5.3 의 DDL 원문). 2단계 게이트 뒤에는 열을 없애거나 이름을 바꾸지 않는다(§A.4).
RECORD_SCHEMA_SQL: str = """PRAGMA journal_mode=WAL;
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS polls (
  poll_id INTEGER PRIMARY KEY AUTOINCREMENT,
  source TEXT NOT NULL,            -- BUS_ARRIVAL, BIKE, SIGNAL
  target_id TEXT NOT NULL,         -- 노선 ID 또는 지역 이름
  window TEXT,                     -- 요청 시각이 든 시연 시간대 이름, 없으면 NULL (active_window)
  t_unix REAL NOT NULL,            -- 요청을 보낸 시각
  ok INTEGER NOT NULL,             -- 1 성공, 0 실패
  n_items INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_polls ON polls(source, target_id, t_unix);
CREATE TABLE IF NOT EXISTS arr_obs (
  poll_id INTEGER NOT NULL, route_id TEXT NOT NULL, st_id TEXT, ars_id TEXT, sta_ord INTEGER,
  slot INTEGER NOT NULL,           -- 1 또는 2 (첫째, 둘째 차량)
  kind TEXT NOT NULL,              -- NORMAL, WAITING, ENDED, NO_INFO (§5.2)
  veh_id TEXT, sect_ord INTEGER, exps REAL, kals REAL, neus REAL,
  mk_unix REAL, full_flag INTEGER, is_last INTEGER, is_arrive INTEGER, arrmsg TEXT,
  term_min REAL, route_type TEXT
);
CREATE INDEX IF NOT EXISTS ix_arr ON arr_obs(route_id, poll_id);
CREATE TABLE IF NOT EXISTS bike_obs (
  poll_id INTEGER NOT NULL, station_id TEXT NOT NULL, bikes INTEGER, racks INTEGER
);
CREATE INDEX IF NOT EXISTS ix_bike ON bike_obs(station_id, poll_id);
CREATE TABLE IF NOT EXISTS sig_obs (
  poll_id INTEGER NOT NULL, signal_src_id TEXT NOT NULL, state TEXT NOT NULL,
  remaining_s REAL NOT NULL, obs_unix REAL
);
CREATE INDEX IF NOT EXISTS ix_sig ON sig_obs(signal_src_id, poll_id);
CREATE TABLE IF NOT EXISTS api_log (
  t_unix REAL NOT NULL, api TEXT NOT NULL,
  target_id TEXT,                  -- 버스는 노선 ID, 쪽으로 나누는 원천은 "쪽 {n}"
  http_status INTEGER,
  latency_ms REAL, error TEXT,
  sample TEXT                      -- API 마다 하루 첫 응답 원문(키는 ***), 그 밖에는 NULL
);
"""

# data/collect_targets.json 이 없을 때 --collect --dry-run 이 보여 주는 예시(§5.3 의 예시와 같다).
DEFAULT_TARGETS_JSON: str = """{
  "poll_s": 60,
  "routes": [{"route_id": "100100025", "name": "146"},
             {"route_id": "100100022", "name": "143"},
             {"route_id": "100100057", "name": "360"},
             {"route_id": "100100019", "name": "140"}],
  "bike_areas": [{"name": "강남역", "lat": 37.4979278, "lon": 127.0275833, "radius_m": 2500},
                 {"name": "삼성역", "lat": 37.5087444, "lon": 127.0635194, "radius_m": 2500}],
  "signal_areas": [{"name": "삼성역", "lat": 37.5087444, "lon": 127.0635194, "radius_m": 600},
                   {"name": "봉은사역", "lat": 37.514210, "lon": 127.060143, "radius_m": 600},
                   {"name": "강남역", "lat": 37.4979278, "lon": 127.0275833, "radius_m": 600},
                   {"name": "신논현역", "lat": 37.50444, "lon": 127.024417, "radius_m": 600}],
  "windows": [{"name": "평일 아침", "day_types": ["WEEKDAY"], "start": "07:30", "end": "09:00"},
              {"name": "평일 저녁", "day_types": ["WEEKDAY"], "start": "18:00", "end": "19:30"}],
  "holidays": ["2026-12-25", "2027-01-01"],
  "daily_call_limits": {"bus_arrival_all": 1000, "signal": 5000, "signal_intersections": 5000},
  "bike_history": {"columns": {"rent_time": "대여일시", "rent_station": "대여대여소ID", "return_time": "반납일시",
                               "return_station": "반납대여소ID", "minutes": "이용시간(분)", "distance_m": "이용거리(M)"},
                   "station_match": "ID_COLUMN"},
  "signal_api": {"enabled": false, "verified": false, "field_map": {
    "items": "body.items.item", "signal_id": "crsrdId", "directions": "nt,et,st,wt,ne,se,sw,nw",
    "state": "{dir}PdsgSttsNm", "remaining": "{dir}PdsgRmndCs", "observed_at": "totDt", "time_format": "%Y%m%d%H%M%S",
    "green_values": "protected-Movement-Allowed,permissive-Movement-Allowed", "red_values": "stop-And-Remain",
    "remaining_scale": "0.1", "remaining_unknown_values": "36001",
    "intersection_items": "body.items.item", "intersection_id": "crsrdId",
    "intersection_lat": "mapCtptIntLat", "intersection_lon": "mapCtptIntLot"}}
}
"""

# 따릉이 대여 이력 CSV 의 열 역할(§1.8.2, §5.3).
BIKE_HISTORY_ROLES: tuple[str, ...] = ("rent_time", "rent_station", "return_time", "return_station", "minutes", "distance_m")

# 신호 필드 표의 역할 열다섯 개(§5.2 의 순서).
SIGNAL_FIELD_ROLES: tuple[str, ...] = (
    "items",
    "signal_id",
    "directions",
    "state",
    "remaining",
    "observed_at",
    "time_format",
    "green_values",
    "red_values",
    "remaining_scale",
    "remaining_unknown_values",
    "intersection_items",
    "intersection_id",
    "intersection_lat",
    "intersection_lon",
)

# 비어 있어도 되는 신호 역할(§5.2). 나머지가 하나라도 비면 신호를 부르지 않는다.
SIGNAL_OPTIONAL_ROLES: tuple[str, ...] = ("directions", "remaining_scale", "remaining_unknown_values")


# ===== 설정 (§0.3, §3.3) =====


def _default_bus_fares() -> dict["BusRouteType", int]:
    return {
        BusRouteType.TRUNK: 1500,
        BusRouteType.BRANCH: 1500,
        BusRouteType.CIRCULAR: 1400,
        BusRouteType.WIDE_AREA: 3000,
        BusRouteType.NIGHT: 2500,
        BusRouteType.VILLAGE: 1200,
    }


class EngineConfig(_Frozen):
    """§0.3 의 모든 파라미터와 §3.3 의 추가 필드. 엔진 코드는 숫자 리터럴 대신 이 값을 쓴다."""

    # 걷기, 따릉이, 판정
    earth_radius_m: PositiveFloat = 6_371_000.0
    gamma: float = Field(default=1.3, ge=1.0)
    v_walk_mps: PositiveFloat = 1.25
    v_pm_mps: PositiveFloat = 4.0
    t_unlock_s: NonNegFloat = 25.0
    t_dock_s: NonNegFloat = 15.0
    bike_pick_min_p: Probability = 0.5
    k_move: NonNegFloat = 0.12
    k_pm: NonNegFloat = 0.12
    safety_buffer_s: NonNegFloat = 30.0
    p_ghost: float = Field(default=0.40, gt=0, lt=1)
    p_safe: float = Field(default=0.75, gt=0, lt=1)
    w_time: NonNegFloat = 0.5
    w_cost: NonNegFloat = 0.2
    w_risk: NonNegFloat = 0.3
    # 탐색 (§1.10)
    max_rides: int = Field(default=4, ge=1, le=5)
    max_bike_legs: int = Field(default=1, ge=0, le=2)
    modes_enabled: tuple[TravelMode, ...] = (TravelMode.BUS, TravelMode.SUBWAY, TravelMode.BIKE)
    max_candidates: int = Field(default=12, ge=1)
    slow_walker_quantile: float = Field(default=0.10, gt=0, lt=0.5)
    horizon_s: PositiveFloat = 7200.0
    snap_max_m: PositiveFloat = 150.0
    full_vehicle_policy: FullVehiclePolicy = FullVehiclePolicy.IGNORE
    rank_criterion: RankCriterion = RankCriterion.MEAN_ARRIVAL
    naive_transfer_wait: NaiveTransferWait = NaiveTransferWait.ZERO
    # 확률 계산 (§1.4)
    m_min: float = Field(default=0.05, gt=0, lt=1)
    m_max: float = Field(default=20.0, gt=1)
    bisect_iters: int = Field(default=30, ge=1)
    n_qmc: int = Field(default=4096, ge=1)
    max_halton_dims: int = Field(default=18, ge=2, le=18)
    hist_bin_s: PositiveFloat = 5.0
    # 차량 시각 (§1.7)
    bus_design_speed_mps: PositiveFloat = 4.1667
    prediction_stale_s: NonNegFloat = 300.0
    timetable_day_start_s: float = Field(default=10_800.0, ge=0, lt=SECONDS_PER_DAY)
    train_lookahead_s: PositiveFloat = 1800.0
    # 신호 학습 (§1.9)
    signal_slot_s: PositiveFloat = 3600.0
    signal_group_s: NonNegFloat = 2.0
    signal_min_gaps: int = Field(default=10, ge=1)
    actuated_iqr_s: NonNegFloat = 5.0
    signal_outage_factor: float = Field(default=1.5, gt=1)
    # 외부 비교와 따릉이 이력 (§5.4, §1.8.2)
    kakao_shortest_diff_warn: PositiveFloat = 0.15
    bike_match_min_rate: Probability = 0.9
    # 요금 (§1.5)
    fare_subway_krw: NonNegInt = 1550
    fare_bus_by_type_krw: dict[BusRouteType, NonNegInt] = Field(default_factory=_default_bus_fares)
    fare_free_distance_km: NonNegFloat = 10.0
    fare_step_km: PositiveFloat = 5.0
    fare_step_krw: NonNegInt = 100
    fare_long_km: NonNegFloat = 50.0
    fare_long_step_km: PositiveFloat = 8.0
    max_rides_per_chain: int = Field(default=5, ge=1)
    bike_pass_krw: NonNegInt = 1000
    bike_mileage_discount_krw: NonNegInt = 500
    climate_card: bool = False
    bike_mileage: bool = False
    transfer_window_s: PositiveFloat = 1800.0
    transfer_window_night_s: PositiveFloat = 3600.0
    transfer_night_from_s: float = Field(default=75_600.0, ge=0, lt=SECONDS_PER_DAY)
    transfer_night_to_s: float = Field(default=25_200.0, ge=0, lt=SECONDS_PER_DAY)
    # §3.3 의 추가 필드
    ellipse_vertices: int = Field(default=72, ge=3)
    api_timeout_s: PositiveFloat = 5.0
    api_retries: int = Field(default=2, ge=0)
    collect_limit_reserve: float = Field(default=0.1, ge=0, lt=1)
    bike_match_radius_m: PositiveFloat = 50.0
    stop_match_radius_m: PositiveFloat = 60.0
    env_seoul_key: NonEmptyStr = ENV_SEOUL_KEY
    env_data_go_kr_key: NonEmptyStr = ENV_DATA_GO_KR_KEY
    env_kakao_key: NonEmptyStr = ENV_KAKAO_KEY
    env_tdata_key: NonEmptyStr = ENV_TDATA_KEY
    data_dir: NonEmptyStr = "data"
    holidays: tuple[str, ...] = ()
    depart_offset_max_s: NonNegFloat = 1800.0

    @model_validator(mode="after")
    def _check_relations(self) -> "EngineConfig":
        if not self.p_ghost < self.p_safe:
            raise ValueError("p_ghost 는 p_safe 보다 작아야 합니다 (0 < p_ghost < p_safe < 1)")
        if self.w_time + self.w_cost + self.w_risk <= 0:
            raise ValueError("가중치 w_time, w_cost, w_risk 의 합은 0 보다 커야 합니다")
        dup = _duplicates([mode.value for mode in self.modes_enabled])
        if dup:
            raise ValueError(f"modes_enabled 에 같은 수단이 두 번 있습니다: {', '.join(dup)}")
        missing = [kind.value for kind in BusRouteType if kind not in self.fare_bus_by_type_krw]
        if missing:
            raise ValueError(f"fare_bus_by_type_krw 에 노선 종류가 빠졌습니다: {', '.join(missing)}")
        if self.fare_long_km < self.fare_free_distance_km:
            raise ValueError("fare_long_km 은 fare_free_distance_km 이상이어야 합니다")
        for day in self.holidays:
            _check_date(day, "휴일")
        return self

    @property
    def normalized_weights(self) -> tuple[float, float, float]:
        """(w_t, w_c, w_r) 를 합이 1 이 되게 정규화한다(§1.11.1). 합은 검증기가 0 보다 크게 보장한다."""
        total = self.w_time + self.w_cost + self.w_risk
        return (self.w_time / total, self.w_cost / total, self.w_risk / total)

    @property
    def m_slow(self) -> float:
        """느린 사람 기준 탐색의 속도 배수 $m_{slow} = 1 + k_{move}\\,\\Phi^{-1}(q_s)$ (§0.3, §1.10.5)."""
        return 1.0 + self.k_move * statistics.NormalDist().inv_cdf(self.slow_walker_quantile)


# ===== 입력 스키마 (§3.3) =====


class Node(_Frozen):
    id: NonEmptyStr
    name: str
    node_type: NodeType
    lat: Latitude
    lon: Longitude
    verified: bool = False
    source: str = ""  # 좌표 근거
    official_id: str | None = None  # 정류소 arsId, 대여소 stationId, 교차로 ID, 역코드
    official_st_id: str | None = None  # 버스 정류소 stId


class BikeStation(Node):
    bikes_available: NonNegInt
    rack_total: NonNegInt
    rental_rate_per_hour: NonNegFloat | None = None  # §1.8, None 이면 P_bike = 1

    @model_validator(mode="after")
    def _check_type(self) -> "BikeStation":
        if self.node_type != NodeType.BIKE_STATION:
            raise ValueError(f"대여소 {self.id}: node_type 은 BIKE_STATION 이어야 합니다")
        return self


class Edge(_Frozen):
    id: NonEmptyStr
    source: NonEmptyStr
    target: NonEmptyStr
    modes: tuple[Mode, ...] = Field(min_length=1)
    kind: EdgeKind
    signal_id: str | None = None
    via: tuple[LatLon, ...] = ()  # 중간 좌표 (위도, 경도)
    distance_m: PositiveFloat | None = None  # None 이면 엔진이 좌표로 계산
    bidirectional: bool = True

    @model_validator(mode="after")
    def _check_modes(self) -> "Edge":
        dup = _duplicates([mode.value for mode in self.modes])
        if dup:
            raise ValueError(f"엣지 {self.id} 의 modes 에 같은 수단이 두 번 있습니다")
        return self


class SignalPhase(_Frozen):
    id: NonEmptyStr
    intersection_id: NonEmptyStr
    direction: str = ""
    green_s: PositiveFloat
    red_s: NonNegFloat
    offset_s: float | None = None
    realtime_open: bool
    official_id: str | None = None
    source: SignalSource = SignalSource.DESIGN
    actuated: bool = False
    gap_samples_s: tuple[PositiveFloat, ...] = ()  # 감응 신호의 주기 표본, 오름차순

    @property
    def cycle_s(self) -> float:
        """주기 = 녹색 + 적색. 감응 신호는 학습이 주기 표본의 중앙값과 같게 맞춰 둔다(§1.9)."""
        return self.green_s + self.red_s

    @model_validator(mode="after")
    def _check_phase(self) -> "SignalPhase":
        cycle = self.green_s + self.red_s
        if self.realtime_open and not self.actuated and self.offset_s is None:
            raise ValueError(f"신호 {self.id}: 개방 신호는 offset_s 가 있어야 합니다")
        if self.offset_s is not None and not 0 <= self.offset_s < cycle:
            raise ValueError(f"신호 {self.id}: offset_s {self.offset_s:g} 는 [0, 주기 {cycle:g}) 안이어야 합니다")
        if self.actuated:
            if not self.gap_samples_s:
                raise ValueError(f"신호 {self.id}: 감응 신호는 gap_samples_s 가 있어야 합니다")
            if not _non_decreasing(self.gap_samples_s):
                raise ValueError(f"신호 {self.id}: gap_samples_s 는 오름차순이어야 합니다")
        elif self.gap_samples_s:
            raise ValueError(f"신호 {self.id}: 감응 신호가 아니면 gap_samples_s 가 비어 있어야 합니다")
        return self


class StopPrediction(_Frozen):
    """버스 정류장 한 순번의 예측 항목(§1.7.1)."""

    rank: int = Field(ge=1, le=2)
    vehicle_id: str
    kind: PredictionKind
    eta_s: float | None = None  # t = 0 기준 도착 예정 초 (관측 경과를 뺀 값)
    is_last: bool = False
    is_full: bool = False
    sect_ord: int | None = None

    @model_validator(mode="after")
    def _check_eta(self) -> "StopPrediction":
        if self.kind == PredictionKind.NORMAL and self.eta_s is None:
            raise ValueError("NORMAL 예측에는 eta_s 가 있어야 합니다")
        if self.kind != PredictionKind.NORMAL and self.eta_s is not None:
            raise ValueError(f"{self.kind.value} 예측에는 eta_s 가 없어야 합니다")
        return self


class BusLine(_Frozen):
    id: NonEmptyStr
    name: str  # 노선 번호, 예 "146"
    route_type: BusRouteType
    real_route: bool
    official_route_id: str | None = None  # busRouteId
    stop_ids: tuple[str, ...] = Field(min_length=2)  # 순번 순 (순환 노선은 같은 정류장이 두 번 나올 수 있다)
    stop_ords: tuple[int, ...] | None = None  # API 의 staOrd
    segment_dist_m: tuple[PositiveFloat, ...]
    headway_s: PositiveFloat | None = None
    last_departure_clock_s: float | None = Field(default=None, ge=0, lt=TWO_DAYS_S)
    predictions: tuple[tuple[StopPrediction, ...], ...]
    prediction_age_s: NonNegFloat | None = None

    @model_validator(mode="after")
    def _check_lengths(self) -> "BusLine":
        n = len(self.stop_ids)
        if len(self.segment_dist_m) != n - 1:
            raise ValueError(f"노선 {self.id}: segment_dist_m 은 정류장 수 − 1 = {n - 1}개여야 합니다")
        if len(self.predictions) != n:
            raise ValueError(f"노선 {self.id}: predictions 는 정류장 수 {n}개여야 합니다")
        if self.stop_ords is not None and len(self.stop_ords) != n:
            raise ValueError(f"노선 {self.id}: stop_ords 는 정류장 수 {n}개여야 합니다")
        for index, items in enumerate(self.predictions):
            if len(items) > 2:
                raise ValueError(f"노선 {self.id}: 순번 {index} 의 예측이 2개를 넘습니다")
            ranks = [item.rank for item in items]
            if len(set(ranks)) != len(ranks):
                raise ValueError(f"노선 {self.id}: 순번 {index} 에 같은 rank 가 두 번 있습니다")
        return self


class SubwayStation(_Frozen):
    key: NonEmptyStr  # 역코드 (OA-101 의 STATION_CD). 환승역처럼 호선마다 다르면 그 가운데 하나
    name: str
    platforms: tuple[tuple[str, str], ...] = Field(min_length=1)  # (호선, 승강장 노드 ID)
    hall_ids: tuple[str, ...] = ()
    exit_ids: tuple[str, ...] = ()
    line_keys: tuple[tuple[str, str], ...] = ()  # (호선, 그 호선의 역코드), key 와 다른 호선만

    @model_validator(mode="after")
    def _check_lines(self) -> "SubwayStation":
        dup = _duplicates([line for line, _ in self.platforms])
        if dup:
            raise ValueError(f"역 {self.key}: 같은 호선의 승강장이 둘 있습니다: {', '.join(dup)}")
        dup = _duplicates([line for line, _ in self.line_keys])
        if dup:
            raise ValueError(f"역 {self.key}: line_keys 에 같은 호선이 둘 있습니다: {', '.join(dup)}")
        lines = {line for line, _ in self.platforms}
        for line, code in self.line_keys:
            if line not in lines:
                raise ValueError(f"역 {self.key}: line_keys 의 호선 {line} 의 승강장이 없습니다")
            if not code.strip():
                raise ValueError(f"역 {self.key}: line_keys 의 호선 {line} 역코드가 비었습니다")
        return self

    def line_key(self, line: str) -> str:
        """그 호선의 역코드(시각표 파일 이름). `line_keys` 에 없으면 `key` 다(§3.3)."""
        return dict(self.line_keys).get(line, self.key)


class SubwayTrip(_Frozen):
    id: NonEmptyStr
    train_no: str
    service_day: DayType
    arr_s: tuple[float, ...]
    dep_s: tuple[float, ...]
    express: bool = False
    destination: str = ""

    @model_validator(mode="after")
    def _check_times(self) -> "SubwayTrip":
        if len(self.arr_s) != len(self.dep_s):
            raise ValueError(f"열차 {self.id}: arr_s 와 dep_s 의 개수가 다릅니다")
        merged: list[float] = []
        for arr, dep in zip(self.arr_s, self.dep_s):
            if arr > dep:
                raise ValueError(f"열차 {self.id}: 도착 {arr:g} 가 출발 {dep:g} 보다 늦습니다")
            merged.extend((arr, dep))
        if not _non_decreasing(tuple(merged)):
            raise ValueError(f"열차 {self.id}: 시각이 순번을 따라 줄어듭니다")
        return self


class SubwayPattern(_Frozen):
    id: NonEmptyStr
    line: NonEmptyStr
    direction: str
    station_keys: tuple[str, ...] = Field(min_length=2)
    platform_ids: tuple[str, ...]
    segment_dist_m: tuple[PositiveFloat, ...]
    distance_verified: tuple[bool, ...]
    trips: tuple[SubwayTrip, ...] = Field(min_length=1)

    @model_validator(mode="after")
    def _check_pattern(self) -> "SubwayPattern":
        n = len(self.station_keys)
        if len(self.platform_ids) != n:
            raise ValueError(f"패턴 {self.id}: platform_ids 는 역 수 {n}개여야 합니다")
        if len(self.segment_dist_m) != n - 1:
            raise ValueError(f"패턴 {self.id}: segment_dist_m 은 역 수 − 1 = {n - 1}개여야 합니다")
        if len(self.distance_verified) != n - 1:
            raise ValueError(f"패턴 {self.id}: distance_verified 는 역 수 − 1 = {n - 1}개여야 합니다")
        for trip in self.trips:
            if len(trip.arr_s) != n:
                raise ValueError(f"패턴 {self.id}: 열차 {trip.id} 의 시각은 역 수 {n}개여야 합니다")
        dup = _duplicates([trip.id for trip in self.trips])
        if dup:
            raise ValueError(f"패턴 {self.id}: 열차 ID 가 겹칩니다: {', '.join(dup)}")
        if not _non_decreasing(tuple(trip.dep_s[0] for trip in self.trips)):
            raise ValueError(f"패턴 {self.id}: 열차는 첫 순번 dep_s 오름차순이어야 합니다")
        return self


class Place(_Frozen):
    name: NonEmptyStr
    node_id: NonEmptyStr


class ExampleTrip(_Frozen):
    """화면의 예시 경로(§3.3, §6.3): 버튼 하나가 출발·목적지 장소를 한 번에 정한다. 엔진은 읽지 않는다."""

    name: NonEmptyStr
    origin_node_id: NonEmptyStr
    destination_node_id: NonEmptyStr
    note: str


class OriginState(_Frozen):
    """출발 상태(§0.1): 지점(노드, 좌표) 또는 지금 탄 차량."""

    kind: OriginKind
    node_id: str | None = None  # AT_NODE
    lat: Latitude | None = None  # AT_POINT
    lon: Longitude | None = None  # AT_POINT
    line_id: str | None = None  # ON_BUS
    pattern_id: str | None = None  # ON_TRAIN
    trip_id: str | None = None  # ON_BUS, ON_TRAIN 에서 탄 차량
    next_index: NonNegInt | None = None  # j_0 (ON_BUS, ON_TRAIN)
    prior_distance_m: NonNegFloat = 0.0  # 차량 안 출발에서 이미 탄 거리 (요금용)

    @model_validator(mode="after")
    def _check_kind(self) -> "OriginState":
        required = {
            OriginKind.AT_NODE: ("node_id",),
            OriginKind.AT_POINT: ("lat", "lon"),
            OriginKind.ON_BUS: ("line_id", "trip_id", "next_index"),
            OriginKind.ON_TRAIN: ("pattern_id", "trip_id", "next_index"),
        }[self.kind]
        for name in ("node_id", "lat", "lon", "line_id", "pattern_id", "trip_id", "next_index"):
            value = getattr(self, name)
            if name in required and value is None:
                raise ValueError(f"{self.kind.value} 출발에는 {name} 값이 있어야 합니다")
            if name not in required and value is not None:
                raise ValueError(f"{self.kind.value} 출발에는 {name} 값을 주지 않습니다")
        return self


class Query(_Frozen):
    origin: OriginState
    destination_node_id: str | None = None
    destination_lat: Latitude | None = None
    destination_lon: Longitude | None = None
    deadline_s: PositiveFloat | None = None  # t = 0 기준 마감

    @model_validator(mode="after")
    def _check_destination(self) -> "Query":
        has_node = self.destination_node_id is not None
        coords = (self.destination_lat is not None, self.destination_lon is not None)
        if coords[0] != coords[1]:
            raise ValueError("목적지 좌표는 위도와 경도를 함께 줍니다")
        if has_node and coords[0]:
            raise ValueError("목적지는 노드 ID 와 좌표 가운데 하나만 줍니다")
        if not has_node and not coords[0]:
            raise ValueError("목적지가 없습니다")
        if (
            self.origin.kind == OriginKind.AT_NODE
            and has_node
            and self.origin.node_id == self.destination_node_id
        ):
            raise ValueError("출발 노드와 목적지 노드가 같습니다")
        return self


_STATION_INSIDE = (NodeType.SUBWAY_PLATFORM, NodeType.STATION_HALL)
_STATION_EDGE_KINDS = (EdgeKind.STATION_PASSAGE, EdgeKind.STAIRS)


class Scenario(_Frozen):
    id: NonEmptyStr
    title: str
    description: str
    nodes: tuple[Node, ...]  # 대여소 제외
    bike_stations: tuple[BikeStation, ...]
    edges: tuple[Edge, ...]
    signals: tuple[SignalPhase, ...]
    bus_lines: tuple[BusLine, ...]
    subway_stations: tuple[SubwayStation, ...]
    subway_patterns: tuple[SubwayPattern, ...]
    places: tuple[Place, ...]
    default_query: Query | None = None
    map_center: LatLon
    map_zoom: int
    sources: tuple[str, ...]
    simulated_time_note: str
    design_roles: dict[str, str] = {}  # 데이터 검사와 설계서가 쓰는 역할 표, 엔진은 읽지 않는다
    examples: tuple[ExampleTrip, ...] = ()  # 화면의 예시 경로(§6.3), 엔진은 읽지 않는다
    data_mode: DataMode = DataMode.SIMULATION
    clock_s: float = Field(ge=0, lt=SECONDS_PER_DAY)  # c_0
    day_type: DayType = DayType.WEEKDAY
    record_note: str = ""
    bike_obs_age_s: NonNegFloat = 0.0

    @model_validator(mode="after")
    def _check_references(self) -> "Scenario":
        node_ids = [node.id for node in self.nodes]
        station_ids = [station.id for station in self.bike_stations]
        dup = _duplicates(node_ids + station_ids)
        if dup:
            raise ValueError(f"노드와 대여소의 ID 가 겹칩니다: {', '.join(dup)}")
        types: dict[str, NodeType] = {node.id: node.node_type for node in self.nodes}
        types.update({station.id: station.node_type for station in self.bike_stations})
        for what, ids in (
            ("엣지", [edge.id for edge in self.edges]),
            ("신호", [signal.id for signal in self.signals]),
            ("역", [station.key for station in self.subway_stations]),
            ("노선과 패턴", [line.id for line in self.bus_lines] + [pattern.id for pattern in self.subway_patterns]),
        ):
            dup = _duplicates(ids)
            if dup:
                raise ValueError(f"{what} ID 가 겹칩니다: {', '.join(dup)}")

        def need(node_id: str, what: str, kinds: tuple[NodeType, ...] | None = None) -> None:
            if node_id not in types:
                raise ValueError(f"{what}: 없는 노드 {node_id} 를 가리킵니다")
            if kinds is not None and types[node_id] not in kinds:
                expected = ", ".join(kind.value for kind in kinds)
                raise ValueError(f"{what}: 노드 {node_id} 의 종류는 {expected} 여야 합니다(지금 {types[node_id].value})")

        signal_ids = {signal.id for signal in self.signals}
        for signal in self.signals:
            need(signal.intersection_id, f"신호 {signal.id}")
        for edge in self.edges:
            need(edge.source, f"엣지 {edge.id}")
            need(edge.target, f"엣지 {edge.id}")
            if edge.signal_id is not None and edge.signal_id not in signal_ids:
                raise ValueError(f"엣지 {edge.id}: 없는 신호 {edge.signal_id} 를 가리킵니다")
            if types[edge.source] in _STATION_INSIDE or types[edge.target] in _STATION_INSIDE:
                if edge.kind not in _STATION_EDGE_KINDS:
                    raise ValueError(f"엣지 {edge.id}: 승강장이나 역 안 노드에 닿는 엣지의 종류는 STATION_PASSAGE 나 STAIRS 여야 합니다")
                if tuple(edge.modes) != (Mode.WALK,):
                    raise ValueError(f"엣지 {edge.id}: 승강장이나 역 안 노드에 닿는 엣지는 보행 전용이어야 합니다")
        for line in self.bus_lines:
            for stop_id in line.stop_ids:
                need(stop_id, f"버스 노선 {line.id}", (NodeType.BUS_STOP,))
        for pattern in self.subway_patterns:
            for platform_id in pattern.platform_ids:
                need(platform_id, f"정차 패턴 {pattern.id}", (NodeType.SUBWAY_PLATFORM,))
        codes = [f"{station.line_key(line)} ({line})" for station in self.subway_stations for line, _ in station.platforms]
        dup = _duplicates(codes)
        if dup:
            raise ValueError(f"역코드와 호선이 두 역에 있습니다: {', '.join(dup)}")
        for station in self.subway_stations:
            for _, platform_id in station.platforms:
                need(platform_id, f"역 {station.key} 의 승강장", (NodeType.SUBWAY_PLATFORM,))
            for hall_id in station.hall_ids:
                need(hall_id, f"역 {station.key} 의 대합실", (NodeType.STATION_HALL,))
            for exit_id in station.exit_ids:
                need(exit_id, f"역 {station.key} 의 출구", (NodeType.STATION_EXIT,))
        for place in self.places:
            need(place.node_id, f"장소 {place.name}")
        if self.default_query is not None:
            self._check_query(self.default_query, need)
        return self

    def _check_query(self, query: Query, need) -> None:
        origin = query.origin
        if origin.kind == OriginKind.AT_NODE and origin.node_id is not None:
            need(origin.node_id, "기본 질의의 출발")
        if query.destination_node_id is not None:
            need(query.destination_node_id, "기본 질의의 목적지")
        if origin.kind == OriginKind.ON_BUS:
            lines = {line.id: line for line in self.bus_lines}
            if origin.line_id not in lines:
                raise ValueError(f"기본 질의: 없는 버스 노선 {origin.line_id} 를 가리킵니다")
            if origin.next_index is not None and origin.next_index >= len(lines[origin.line_id].stop_ids):
                raise ValueError(f"기본 질의의 next_index {origin.next_index} 가 노선 {origin.line_id} 의 순번 밖입니다")
        if origin.kind == OriginKind.ON_TRAIN:
            patterns = {pattern.id: pattern for pattern in self.subway_patterns}
            if origin.pattern_id not in patterns:
                raise ValueError(f"기본 질의: 없는 정차 패턴 {origin.pattern_id} 를 가리킵니다")
            pattern = patterns[origin.pattern_id]
            if origin.trip_id not in {trip.id for trip in pattern.trips}:
                raise ValueError(f"기본 질의: 패턴 {pattern.id} 에 없는 열차 {origin.trip_id} 를 가리킵니다")
            if origin.next_index is not None and origin.next_index >= len(pattern.station_keys):
                raise ValueError(f"기본 질의의 next_index {origin.next_index} 가 패턴 {pattern.id} 의 순번 밖입니다")


# ===== 결과 스키마 (§3.3) =====


class SignalEvent(_Frozen):
    signal_id: str
    t_arr_s: float
    tau_s: float | None  # 표본 신호면 None
    state: SignalState
    wait_s: NonNegFloat
    var_s2: NonNegFloat
    source: SignalSource
    actuated: bool


class PathResult(_Frozen):
    node_ids: tuple[str, ...]
    edge_ids: tuple[str, ...]
    polyline: tuple[LatLon, ...]
    distance_m: NonNegFloat
    t_start_s: float
    t_end_s: float
    travel_s: NonNegFloat
    wait_s: NonNegFloat
    events: tuple[SignalEvent, ...]


class BikeSegment(_Frozen):
    pick_id: str
    drop_id: str
    walk_in: PathResult  # ① 대여소까지 걷기
    ride: PathResult  # ③ 주행
    walk_out: PathResult  # ⑤ 반납 뒤 걷기
    unlock_s: NonNegFloat
    dock_s: NonNegFloat
    arrival_at_pick_s: float  # a_b
    obs_age_s: NonNegFloat  # g
    p_bike: Probability
    fallback: PathResult | None  # 대여소 → 이동 도착점 최단거리 (계획 시각으로 전파)


class Move(_Frozen):
    index: NonNegInt  # 0 ~ K
    from_id: str
    to_id: str
    walk: PathResult | None  # 따릉이 없는 이동
    bike: BikeSegment | None
    t_start_s: float
    t_end_s: float
    distance_m: NonNegFloat  # 걷기와 주행을 더한 값
    walk_distance_m: NonNegFloat


class VehicleOption(_Frozen):
    trip_id: str
    route_id: str  # 그 차량의 노선 ID 또는 패턴 ID (묶음이면 차량마다 다를 수 있다, §1.7.4)
    ordinal: int = Field(ge=1)  # 그 차량 노선의 승차 순번에서 몇 번째 차 (§1.7.1)
    dep_s: float
    alight_arr_s: float
    time_source: TimeSource  # 승차 순번의 출처
    is_full: bool  # 승차 순번의 만차 상태 (§1.7.3)
    is_last: bool
    p_catch: Probability


class BundleLine(_Frozen):
    """탑승 묶음의 노선 하나(§1.7.4 (2)): 그 노선의 승차·하차 순번."""

    route_id: str
    route_name: str  # Ride.route_name 과 같은 규칙
    board_index: NonNegInt
    alight_index: NonNegInt


class Ride(_Frozen):
    index: int = Field(ge=1)  # 1 ~ K
    mode: TravelMode  # BUS 또는 SUBWAY
    route_id: str  # 버스 노선 ID 또는 패턴 ID
    route_name: str  # 버스는 노선 번호, 지하철은 "{호선} {방향} {마지막 역 이름}행"
    bus_type: BusRouteType | None
    board_index: NonNegInt | None  # 차량 안 출발의 첫 탑승은 None
    alight_index: NonNegInt
    board_node_id: str | None
    alight_node_id: str
    distance_m: NonNegFloat
    # 계획(§1.10.6)이 막차를 놓친 탑승과 그 뒤의 탑승은 계획 값이 없다(None).
    plan_trip_id: str | None
    plan_stop_arrival_s: float | None
    plan_dep_s: float | None
    plan_arr_s: float | None
    plan_wait_s: NonNegFloat | None
    fallback: PathResult | None  # 승차 정류장 → D 최단거리 (막차 놓침용)
    # 묶음(§1.7.4)의 노선들(노선 ID 순)과 화면 이름. 노선이 하나뿐인 탑승은 빈 튜플과 "" 이다.
    # 묶음이면 route_id ~ distance_m 은 계획 차량의 노선(계획이 막차를 놓쳤으면 묶음의 첫 노선)의 값이다.
    bundle: tuple[BundleLine, ...] = ()
    bundle_name: str = ""

    @model_validator(mode="after")
    def _check_mode(self) -> "Ride":
        if self.mode == TravelMode.BIKE:
            raise ValueError("탑승의 수단은 BUS 나 SUBWAY 입니다")
        return self


class MarginHistogram(_Frozen):
    bin_width_s: PositiveFloat
    bins: tuple[tuple[float, NonNegInt], ...]  # (칸의 왼쪽 경계, 점 수)
    n_points: NonNegInt
    n_under: NonNegInt
    n_over: NonNegInt
    n_infinite: NonNegInt
    success_mass: Probability


class BoardingAssessment(_Frozen):
    ride_index: int = Field(ge=1)
    guided_trip_id: str | None
    guided_found: bool
    q_joint: Probability  # Q_l(g_l)
    p_conditional: Probability
    vehicles: tuple[VehicleOption, ...] = Field(max_length=6)  # §1.4.5 (2)
    trip_distribution: tuple[tuple[str, Probability], ...]  # 유효 차량열 순(§1.7.4), 맨 뒤 "MISSED_LAST"
    naive_trip_id: str | None
    naive_stop_arrival_s: float | None
    naive_margin_s: float | None
    p_catch_naive: Probability | None
    ghost: bool
    histogram: MarginHistogram | None


class ArrivalStats(_Frozen):
    mean_s: float | None
    p10_s: float | None
    p50_s: float | None
    p90_s: float | None
    p_on_time: Probability | None
    p_unreachable: Probability
    method: ProbMethod
    n_points: NonNegInt
    n_sampled_signals: NonNegInt
    capped_signal_ids: tuple[str, ...]
    bike_fallback_mass: tuple[Probability, ...]  # 따릉이 구간마다 대체 보행의 무게
    missed_last_mass: Probability  # 어느 탑승에서든 막차를 놓친 점의 무게(처음부터 가지 못한 점은 넣지 않는다)


class FareChain(_Frozen):
    ride_indexes: tuple[int, ...] = Field(min_length=1)  # 합친 지하철 탑승은 함께
    base_krw: NonNegInt
    distance_m: NonNegFloat
    distance_extra_krw: NonNegInt
    break_reason: Literal["WINDOW", "MAX_RIDES", "SAME_LINE", "SUBWAY_OUTSIDE"] | None


class FareBreakdown(_Frozen):
    chains: tuple[FareChain, ...]
    transit_krw: NonNegInt
    bike_krw: NonNegInt
    mileage_discount_krw: NonNegInt
    climate_card_applied: bool
    total_krw: int


class UtilityTerms(_Frozen):
    time_term: float
    cost_term: float
    risk_term: float  # w_r (1 - P*)
    total: float  # J
    t_max_s: float
    cost_max_krw: float
    weights: tuple[float, float, float]


class Leg(_Frozen):
    kind: LegKind
    start_s: float
    end_s: float
    distance_m: NonNegFloat
    from_id: str
    to_id: str
    label: str


class ItineraryResult(_Frozen):
    itinerary_id: NonEmptyStr
    label: str
    found_by: tuple[SearchRun, ...]
    structure_key: str  # 구조 키의 JSON
    ride_key: str  # 대표 묶기 키의 JSON
    moves: tuple[Move, ...]
    rides: tuple[Ride, ...]
    legs: tuple[Leg, ...]
    plan_arrival_s: float | None  # 계획이 D 에 닿지 못하면 None
    plan_missed_last: bool
    boardings: tuple[BoardingAssessment, ...]
    p_bikes: tuple[Probability, ...]
    p_star: Probability
    grade: Grade
    arrival: ArrivalStats
    status: RouteStatus
    reasons: tuple[ReasonCode, ...]
    naive_promised_s: float | None
    ghost_count: NonNegInt
    fare: FareBreakdown
    utility: UtilityTerms | None  # UTILITY 기준의 RANKED 여정만
    criterion_value: float | None  # RANKED 여정만, 걸러진 여정은 None
    walk_distance_m: NonNegFloat
    rank: int | None = Field(default=None, ge=1)
    representative_id: str | None = None  # 다른 걷는 길이면 그 대표
    variant_ids: tuple[str, ...] = ()  # 대표면 그 아래 여정들


class LineTimes(_Frozen):
    route_id: str
    mode: TravelMode
    run_s: tuple[float, ...]  # 버스는 구간 운행시간 r_i, 지하철은 pi_arr(i+1) - pi_dep(i)
    run_source: tuple[RunTimeSource, ...]  # 버스만, 지하철은 빈 튜플
    trip_ids: tuple[str, ...]
    n_known: NonNegInt
    n_synthetic: NonNegInt
    usable: bool


class SearchRoundTrace(_Frozen):
    round: NonNegInt
    new_labels: NonNegInt
    marked_stops: NonNegInt
    routes_scanned: NonNegInt
    best_d_s: float | None


class SearchRunTrace(_Frozen):
    run: SearchRun
    skipped: bool
    skip_reason: str
    modes: tuple[TravelMode, ...]
    m_run: PositiveFloat
    wait_rule: WaitRule
    bike_limit: NonNegInt
    buffer_s: NonNegFloat
    rounds: tuple[SearchRoundTrace, ...]
    d_labels: tuple[tuple[float, NonNegInt, NonNegInt], ...]  # (도착, 탑승 수, 따릉이 수)
    itinerary_ids: tuple[str, ...]


class SearchSummary(_Frozen):
    runs: tuple[SearchRunTrace, ...]
    found_total: NonNegInt
    distinct: NonNegInt
    kept: NonNegInt
    discarded_ids: tuple[str, ...]
    reach: tuple[tuple[str, NonNegInt, float], ...]  # FULL 의 (노드 ID, 처음 닿은 라운드, 가장 이른 시각)


class StationStatus(_Frozen):
    station_id: str
    use: StationUse
    bikes_available: NonNegInt
    arrival_s: float | None
    p_bike: Probability | None


class ComparisonPanel(_Frozen):
    naive_best_id: str | None
    best_id: str | None
    same: bool
    naive_promised_s: float | None
    naive_mean_s: float | None
    naive_p90_s: float | None
    naive_p_star: Probability | None
    naive_status: RouteStatus | None
    naive_reasons: tuple[ReasonCode, ...]
    best_mean_s: float | None
    best_p90_s: float | None
    late_vs_promise_s: float | None
    saving_s: float | None
    app_misled: bool


class PruningRecord(_Frozen):
    node_id: str
    d_s_m: NonNegFloat
    d_d_m: NonNegFloat
    sum_m: NonNegFloat
    threshold_m: NonNegFloat
    kept: bool
    kept_for_transfer: bool  # 타원 밖이지만 승하차·역 안 노드라 남김 (§1.1)


class PruningSummary(_Frozen):
    d_sd_m: NonNegFloat
    threshold_m: NonNegFloat
    a_m: NonNegFloat
    b_m: NonNegFloat
    kept_count: NonNegInt
    total_count: NonNegInt
    polygon: tuple[LatLon, ...]


class EngineWarning(_Frozen):
    code: WarningCode
    message: str  # 한국어
    ref_ids: tuple[str, ...] = ()


class ApiSourceStatus(_Frozen):
    """(원천, 대상)마다 하나. BUS_ARRIVAL (대상 순), BIKE, SIGNAL, SUBWAY_TIMETABLE 순으로 늘어놓는다."""

    source: SourceKind
    target: str = ""  # 버스 도착은 노선 공식 ID, 따릉이·신호는 재생에서 지역 이름이고 실시간에서 ""
    state: SourceState
    reason: str
    attempts: NonNegInt
    fetched_count: NonNegInt
    matched_count: NonNegInt
    observed_at: str | None  # ISO 8601 (§4.8)
    issues: tuple[EngineWarning, ...] = ()


class EngineOutput(_Frozen):
    scenario_id: str
    query: Query
    status: EngineStatus
    config: EngineConfig
    origin_node_id: str | None
    destination_node_id: str | None
    pruning: PruningSummary | None  # 붙이기 실패면 None
    pruning_records: tuple[PruningRecord, ...]
    line_times: tuple[LineTimes, ...]
    search: SearchSummary
    itineraries: tuple[ItineraryResult, ...]  # 평가한 후보 전부, 여정 ID 순
    ranking: tuple[str, ...]  # 대표 여정 ID, 순위 순
    pruned_ids: tuple[str, ...]  # 걸러진 여정, 평균 도착 순
    best_id: str | None
    comparison: ComparisonPanel
    stations: tuple[StationStatus, ...]
    warnings: tuple[EngineWarning, ...]
    sources: tuple[ApiSourceStatus, ...]
    unverified_node_ids: tuple[str, ...]
    data_mode: DataMode
    clock_s: float
    day_type: DayType


# ===== 공공 API 명세 (§5.2) =====


class ApiSpec(_Frozen):
    """공공 API 와 카카오 API 의 주소, 파라미터, 응답 필드, 단위, 쪽 나누기, 오류 표시, 확인 수준(§5.2).

    주소의 `{KEY}` 는 키 자리(PATH), `{start}`, `{end}` 는 쪽 범위(RANGE), 나머지 `{이름}` 은 `params` 의 값이다.
    경로(`items_path`, `error_paths`, `error_message_paths`)는 점으로 구분한 후보이고 처음 찾은 것을 쓴다.
    """

    api: NonEmptyStr
    url: NonEmptyStr
    key_place: Literal["PATH", "QUERY", "HEADER"]
    key_param: str | None = None  # QUERY 면 파라미터 이름, HEADER 면 헤더 이름
    key_format: NonEmptyStr = "{KEY}"  # 키 값의 형식 (카카오 "KakaoAK {KEY}")
    key_env: NonEmptyStr  # 키를 읽을 환경변수 이름
    params: tuple[str, ...] = ()  # 요청 파라미터 이름(주소의 자리 표시 포함)
    fixed_params: dict[str, str] = {}
    paging: Literal["RANGE", "PAGE_NO"] | None = None
    page_size: int | None = Field(default=None, ge=1)
    max_pages: int | None = Field(default=None, ge=1)
    expected_pages: int = Field(default=1, ge=1)  # 호출 계획의 쪽 수 어림 (§5.3)
    items_path: tuple[str, ...] = ()
    fields: dict[str, str] = {}  # 역할 → 응답 필드 이름. {slot} 은 차량 칸 번호(1, 2)
    units: dict[str, str] = {}
    error_paths: tuple[str, ...] = ()
    error_ok_values: tuple[str, ...] = ()
    no_data_values: tuple[str, ...] = ()
    error_message_paths: tuple[str, ...] = ()
    verified: bool
    evidence: NonEmptyStr  # 출처와 확인 날짜 YYYY-MM-DD

    @model_validator(mode="after")
    def _check_spec(self) -> "ApiSpec":
        placeholders = _URL_FIELD_RE.findall(self.url)
        if self.key_place == "PATH":
            if "KEY" not in placeholders or self.key_param is not None:
                raise ValueError(f"{self.api}: 주소에 키를 넣는 API 는 url 에 {{KEY}} 가 있고 key_param 이 없어야 합니다")
        else:
            if not self.key_param:
                raise ValueError(f"{self.api}: 키를 넣을 파라미터나 헤더 이름이 없습니다")
            if "KEY" in placeholders:
                raise ValueError(f"{self.api}: 주소에 {{KEY}} 를 넣는 것은 PATH 방식뿐입니다")
        if "{KEY}" not in self.key_format:
            raise ValueError(f"{self.api}: key_format 에 {{KEY}} 가 있어야 합니다")
        unknown = [name for name in placeholders if name != "KEY" and name not in self.params]
        if unknown:
            raise ValueError(f"{self.api}: 주소의 자리 표시가 params 에 없습니다: {', '.join(unknown)}")
        unknown = [name for name in self.fixed_params if name not in self.params]
        if unknown:
            raise ValueError(f"{self.api}: fixed_params 의 이름이 params 에 없습니다: {', '.join(unknown)}")
        if self.paging is not None and self.page_size is None:
            raise ValueError(f"{self.api}: 쪽을 나누는 API 는 page_size 가 있어야 합니다")
        if self.paging == "RANGE" and not {"start", "end"} <= set(placeholders):
            raise ValueError(f"{self.api}: RANGE 쪽 나누기는 주소에 {{start}}, {{end}} 가 있어야 합니다")
        if self.paging == "PAGE_NO" and not {"pageNo", "numOfRows"} <= set(self.params):
            raise ValueError(f"{self.api}: PAGE_NO 쪽 나누기는 params 에 pageNo, numOfRows 가 있어야 합니다")
        if self.max_pages is not None and self.expected_pages > self.max_pages:
            raise ValueError(f"{self.api}: expected_pages 가 max_pages 보다 큽니다")
        if (self.error_ok_values or self.no_data_values or self.error_message_paths) and not self.error_paths:
            raise ValueError(f"{self.api}: 오류 표시 필드(error_paths) 없이 정상·자료 없음 값이나 문구 필드가 있습니다")
        if not _DATE_IN_TEXT_RE.search(self.evidence):
            raise ValueError(f"{self.api}: 근거에 확인 날짜(YYYY-MM-DD)가 있어야 합니다")
        return self


_BUS_ERROR_PATHS = ("msgHeader.headerCd", "cmmMsgHeader.returnReasonCode")
_BUS_ERROR_MESSAGES = ("msgHeader.headerMsg", "cmmMsgHeader.returnAuthMsg", "cmmMsgHeader.errMsg")
_SIGNAL_ERROR_PATHS = ("header.resultCode", "cmmMsgHeader.returnReasonCode")
_SIGNAL_ERROR_MESSAGES = ("header.resultMsg", "cmmMsgHeader.returnAuthMsg", "cmmMsgHeader.errMsg")
_SIGNAL_PARAMS = ("stdgCd", "pageNo", "numOfRows", "type")
_SIGNAL_FIXED = {"stdgCd": "1100000000", "type": "JSON"}
_WGS84 = "도(WGS84)"

API_SPECS: MappingProxyType = MappingProxyType(
    {
        spec.api: spec
        for spec in (
            ApiSpec(
                api="bus_arrival_all",
                url="http://ws.bus.go.kr/api/rest/arrive/getArrInfoByRouteAll",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=("busRouteId",),
                items_path=("msgBody.itemList",),
                fields={
                    "st_id": "stId",
                    "ars_id": "arsId",
                    "sta_ord": "staOrd",
                    "stop_name": "stNm",
                    "route_name": "rtNm",
                    "route_type": "routeType",
                    "term": "term",
                    "mk_tm": "mkTm",
                    "veh_id": "vehId{slot}",
                    "exps": "exps{slot}",
                    "kals": "kals{slot}",
                    "neus": "neus{slot}",
                    "sect_ord": "sectOrd{slot}",
                    "full": "full{slot}",
                    "is_arrive": "isArrive{slot}",
                    "is_last": "isLast{slot}",
                    "arrmsg": "arrmsg{slot}",
                },
                units={
                    "term": "분",
                    "exps": "초",
                    "kals": "초",
                    "neus": "초",
                    "mk_tm": "YYYY-MM-DD HH:MM:SS.f (한국 표준시)",
                },
                error_paths=_BUS_ERROR_PATHS,
                error_ok_values=("0",),
                error_message_paths=_BUS_ERROR_MESSAGES,
                verified=False,
                evidence=(
                    "공공데이터포털 15000314 공식 페이지(요청 변수, XML, exps·kals·neus 초, full 만차여부)와 실제 응답 "
                    "2026-11-18 14:32 (146, 포털 미리보기, headerCd 0, 135행, mkTm 형식, staOrd − sectOrd1)으로 "
                    "확인(아스트라 4·5단위). 확인 필요: isLast1·isLast2, 기점 막차 시각 필드, 운행종료 문구, "
                    "kals·neus 빈 값, full 의 운용 뜻, 오류 때 headerCd (§5.2)."
                ),
            ),
            ApiSpec(
                api="route_stations",
                url="http://ws.bus.go.kr/api/rest/busRouteInfo/getStaionByRoute",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=("busRouteId",),
                items_path=("msgBody.itemList",),
                fields={
                    "seq": "seq",
                    "st_id": "station",
                    "station_no": "stationNo",
                    "ars_id": "arsId",
                    "name": "stationNm",
                    "lon": "gpsX",
                    "lat": "gpsY",
                    "direction": "direction",
                },
                units={"lon": _WGS84, "lat": _WGS84},
                error_paths=_BUS_ERROR_PATHS,
                error_ok_values=("0",),
                error_message_paths=_BUS_ERROR_MESSAGES,
                verified=False,
                evidence=(
                    "공공데이터포털 15000193 공식 상세 명세로 오퍼레이션(철자 Staion)과 필드 확인, 2026-11-18 "
                    "(아스트라 5단위). 실제 응답 표본은 없다. 확인 필요: arsId 와 stationNo, seq 와 staOrd."
                ),
            ),
            ApiSpec(
                api="station_by_pos",
                url="http://ws.bus.go.kr/api/rest/stationinfo/getStationByPos",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=("tmX", "tmY", "radius"),
                items_path=("msgBody.itemList",),
                fields={
                    "ars_id": "arsId",
                    "st_id": "stationId",
                    "name": "stationNm",
                    "lon": "gpsX",
                    "lat": "gpsY",
                    "dist": "dist",
                },
                units={"tmX": "경도(WGS84)", "tmY": "위도(WGS84)", "radius": "m", "dist": "m (추정)", "lon": _WGS84, "lat": _WGS84},
                error_paths=_BUS_ERROR_PATHS,
                error_ok_values=("0",),
                error_message_paths=_BUS_ERROR_MESSAGES,
                verified=True,
                evidence=(
                    "공공데이터포털 15000303 공식 페이지와 서울시 활용가이드(2025-09-24)로 확인, 2026-11-18. "
                    "dist 의 단위 m 는 가이드 예시 세 건의 계산과 맞아 추정한 값이다. 정류소 식별자 확인에만 쓴다."
                ),
            ),
            ApiSpec(
                api="station_by_uid",
                url="http://ws.bus.go.kr/api/rest/stationinfo/getStationByUid",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=("arsId",),
                items_path=("msgBody.itemList",),
                fields={"ars_id": "arsId", "st_id": "stId", "name": "stNm", "lon": "gpsX", "lat": "gpsY"},
                units={"lon": _WGS84, "lat": _WGS84},
                error_paths=_BUS_ERROR_PATHS,
                error_ok_values=("0",),
                error_message_paths=_BUS_ERROR_MESSAGES,
                verified=False,
                evidence=(
                    "공공데이터포털 15000303 공식 페이지와 서울시 활용가이드(2025-09-24)로 요청 변수(arsId, 5자리)를 "
                    "확인, 2026-11-18. 응답 필드 이름은 실제 응답으로 확인 필요. 정류소 식별자 확인에만 쓴다."
                ),
            ),
            ApiSpec(
                api="bike_list",
                url="http://openapi.seoul.go.kr:8088/{KEY}/json/bikeList/{start}/{end}/",
                key_place="PATH",
                key_env=ENV_SEOUL_KEY,
                params=("start", "end"),
                paging="RANGE",
                page_size=1000,
                max_pages=10,
                expected_pages=3,
                items_path=("rentBikeStatus.row",),
                fields={
                    "station_id": "stationId",
                    "station_name": "stationName",
                    "racks": "rackTotCnt",
                    "bikes": "parkingBikeTotCnt",
                    "shared": "shared",
                    "lat": "stationLatitude",
                    "lon": "stationLongitude",
                },
                units={"racks": "대", "bikes": "대", "shared": "% (100 을 넘기도 한다)", "lat": _WGS84, "lon": _WGS84},
                error_paths=("rentBikeStatus.RESULT.CODE", "RESULT.CODE"),
                error_ok_values=("INFO-000",),
                no_data_values=("INFO-200",),
                error_message_paths=("rentBikeStatus.RESULT.MESSAGE", "RESULT.MESSAGE"),
                verified=True,
                evidence=(
                    "실제 응답 2026-11-18 20:52 KST (사용자의 일반 인증키, 아스트라 8단위): INFO-000, 쪽마다 "
                    "1,000·1,000·742행, 고유 stationId 2,742개, 2743 ~ 3742 는 0행. 잘못된 키는 JSON 요청에도 "
                    "XML RESULT/CODE INFO-100."
                ),
            ),
            ApiSpec(
                api="subway_timetable",
                url=(
                    "http://openapi.seoul.go.kr:8088/{KEY}/json/SearchSTNTimeTableByIDService/"
                    "{start}/{end}/{station_cd}/{week_tag}/{inout_tag}/"
                ),
                key_place="PATH",
                key_env=ENV_SEOUL_KEY,
                params=("start", "end", "station_cd", "week_tag", "inout_tag"),
                paging="RANGE",
                page_size=1000,
                max_pages=5,
                expected_pages=1,
                items_path=("SearchSTNTimeTableByIDService.row",),
                fields={
                    "line": "LINE_NUM",
                    "station_cd": "STATION_CD",
                    "station_nm": "STATION_NM",
                    "week_tag": "WEEK_TAG",
                    "inout_tag": "INOUT_TAG",
                    "train_no": "TRAIN_NO",
                    "arrive": "ARRIVETIME",
                    "depart": "LEFTTIME",
                    "origin_station": "ORIGINSTATION",
                    "dest_station": "DESTSTATION",
                    "destination": "SUBWAYENAME",
                    "express": "EXPRESS_YN",
                },
                units={
                    "arrive": "HH:MM:SS (자정을 넘긴 운행은 24·25시, 시발역 도착은 00:00:00)",
                    "depart": "HH:MM:SS (종착역 출발은 00:00:00)",
                    "week_tag": "1 평일, 2 토요일, 3 일요일·공휴일",
                    "inout_tag": "1 상행(내선), 2 하행(외선)",
                },
                error_paths=("SearchSTNTimeTableByIDService.RESULT.CODE", "RESULT.CODE"),
                error_ok_values=("INFO-000",),
                no_data_values=("INFO-200",),
                error_message_paths=("SearchSTNTimeTableByIDService.RESULT.MESSAGE", "RESULT.MESSAGE"),
                verified=True,
                evidence=(
                    "실제 응답 2026-11-18 21:09 KST (사용자의 일반 인증키, 아스트라 8단위): 삼성 0219 평일 방향 1·2 가 "
                    "240·241행, 강남 0222 가 239·240행, INFO-000, 시각은 초까지. 신분당선은 INFO-200. 확인 필요: "
                    "EXPRESS_YN \"D\" 의 공식 뜻, TRAIN_NO 가 여러 역에서 같은 열차인지(아스트라 31단위)."
                ),
            ),
            ApiSpec(
                api="signal",
                url="https://apis.data.go.kr/B551982/rti/tl_drct_info",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=_SIGNAL_PARAMS,
                fixed_params=_SIGNAL_FIXED,
                paging="PAGE_NO",
                page_size=1000,
                max_pages=10,
                expected_pages=3,
                items_path=("body.items.item",),
                fields={
                    "signal_id": "crsrdId",
                    "observed_at": "totDt",
                    "state": "{dir}PdsgSttsNm",
                    "remaining": "{dir}PdsgRmndCs",
                },
                units={"remaining": "0.1초 (추정, --status 의 남은 시간 검산으로 확정)", "observed_at": "YYYYMMDDHHMMSS (한국 표준시)"},
                error_paths=_SIGNAL_ERROR_PATHS,
                error_ok_values=("K0",),
                error_message_paths=_SIGNAL_ERROR_MESSAGES,
                verified=False,
                evidence=(
                    "공공데이터포털 15157604 공식 명세와 공개된 실제 응답 10행(2026-06-05, totalCount 2,581)으로 구조 "
                    "확인(아스트라 7단위, 2026-11-18). 사용자 키로 받은 응답은 아직 없다. 실제 필드 이름은 수집 대상 "
                    "파일의 signal_api.field_map 을 쓴다."
                ),
            ),
            ApiSpec(
                api="signal_intersections",
                url="https://apis.data.go.kr/B551982/rti/crsrd_map_info",
                key_place="QUERY",
                key_param="serviceKey",
                key_env=ENV_DATA_GO_KR_KEY,
                params=_SIGNAL_PARAMS,
                fixed_params=_SIGNAL_FIXED,
                paging="PAGE_NO",
                page_size=1000,
                max_pages=10,
                expected_pages=3,
                items_path=("body.items.item",),
                fields={"intersection_id": "crsrdId", "name": "crsrdNm", "lat": "mapCtptIntLat", "lon": "mapCtptIntLot"},
                units={"lat": _WGS84, "lon": _WGS84},
                error_paths=_SIGNAL_ERROR_PATHS,
                error_ok_values=("K0",),
                error_message_paths=_SIGNAL_ERROR_MESSAGES,
                verified=False,
                evidence=(
                    "공공데이터포털 15157604 공식 명세로 오퍼레이션과 필드 확인(아스트라 7단위, 2026-11-18). "
                    "사용자 키로 받은 응답은 아직 없다. 실제 필드 이름은 signal_api.field_map 을 쓴다."
                ),
            ),
            ApiSpec(
                api="signal_tdata",
                url="https://t-data.seoul.go.kr/apig/apiman-gateway/tapi/v2xSignalPhaseTimingFusionInformation/1.0",
                key_place="QUERY",
                key_param="apiKey",
                key_env=ENV_TDATA_KEY,
                params=("type", "pageNo", "numOfRows", "itstId"),
                fixed_params={"type": "json", "pageNo": "1", "numOfRows": "1000"},
                items_path=("items",),
                fields={
                    "signal_id": "itstId",
                    "observed_at": "trsmUtcTime",
                    "state": "{dir}PdsgStatNm",
                    "remaining": "{dir}PdsgRmdrCs",
                },
                units={"remaining": "0.1초 (1초에 10 씩 준다, 2026-11-21 실측)", "observed_at": "유닉스 밀리초(UTC)"},
                verified=True,
                evidence=(
                    "실제 응답 2026-11-22 01:05 KST (사용자의 t-data 키, 사용자 PC): 교차로 1537 에 HTTP 200, 맨 위가 JSON 배열"
                    "(머리말·건수 없음), 239행, trsmUtcTime 오름차순, 가장 최신 행이 부른 시각보다 0.7초 앞, 행 간격 1초. "
                    "방향 nt·et·st·wt·ne·se·sw·nw 마다 Pdsg(보행) 등 여섯 신호의 RmdrCs·StatNm. 같은 키로 300초 안에 다시 "
                    "부르면 HTTP 429 V2X_REPEAT_CALL_LIMIT, 강남 교차로(2968, 3010)는 HTTP 500 (2026-11-21 00:30 KST)."
                ),
            ),
            ApiSpec(
                api="kakao_walk",
                url="https://dapi.kakao.com/v2/routing/walk",
                key_place="HEADER",
                key_param="Authorization",
                key_format="KakaoAK {KEY}",
                key_env=ENV_KAKAO_KEY,
                params=("start_x", "start_y", "end_x", "end_y", "route_mode"),
                items_path=("route",),
                fields={
                    "total_distance": "properties.totalDistance",
                    "total_time": "properties.totalTime",
                    "legs": "legs",
                    "steps": "steps",
                    "guidance": "guidance",
                    "distance": "distance",
                    "time": "time",
                    "x": "x",
                    "y": "y",
                },
                units={
                    "total_distance": "m",
                    "total_time": "초",
                    "distance": "m",
                    "time": "초",
                    "x": "경도(WGS84)",
                    "y": "위도(WGS84)",
                    "start_x": "경도(WGS84)",
                    "start_y": "위도(WGS84)",
                },
                verified=True,
                evidence=(
                    "카카오 디벨로퍼스 공식 문서와 데브톡 답변(2026-09-01)으로 확인, 2026-11-18. route_mode 는 "
                    "BROAD_FIRST(기본), SHORTEST, ACCESSIBLE. 응답 저장과 반복 사용 금지(§5.4)."
                ),
            ),
        )
    }
)


# ===== 수집 스키마 (§3.3, §5.3) =====


class TargetRoute(_Frozen):
    route_id: str  # busRouteId. 빈 값은 스키마가 받고 --collect 가 거부한다(§3.7)
    name: str


class TargetArea(_Frozen):
    name: NonEmptyStr
    lat: Latitude
    lon: Longitude
    radius_m: PositiveFloat


class DemoWindow(_Frozen):
    name: NonEmptyStr
    day_types: tuple[DayType, ...] = Field(min_length=1)
    start: str  # "HH:MM"
    end: str  # "HH:MM", 같은 날 안에서 start 보다 늦다

    @model_validator(mode="after")
    def _check_window(self) -> "DemoWindow":
        _check_hhmm(self.start, f"시간대 {self.name} 의 start")
        _check_hhmm(self.end, f"시간대 {self.name} 의 end")
        if _hhmm_minutes(self.start) >= _hhmm_minutes(self.end):
            raise ValueError(f"시간대 {self.name}: start 가 end 보다 앞서야 합니다(같은 날 안)")
        return self


class BikeHistorySpec(_Frozen):
    columns: dict[str, str]  # 역할 → CSV 열 이름
    station_match: Literal["NAME_PREFIX_NUMBER", "ID_COLUMN"]

    @model_validator(mode="after")
    def _check_roles(self) -> "BikeHistorySpec":
        unknown = sorted(set(self.columns) - set(BIKE_HISTORY_ROLES))
        if unknown:
            raise ValueError(f"bike_history.columns 에 모르는 역할이 있습니다: {', '.join(unknown)}")
        return self


class SignalApiSpec(_Frozen):
    enabled: bool = False
    verified: bool = False
    source: Literal["DATA_GO_KR", "TDATA"] = "DATA_GO_KR"  # 전국 API(지역 한꺼번에) 또는 서울 t-data(교차로마다, 31단계)
    min_call_interval_s: float = Field(default=0.0, ge=0)  # 같은 프로세스에서 신호 API 를 부르는 최소 간격(t-data 300초)
    field_map: dict[str, str] = {}  # 역할 → 필드 이름 (§5.2)

    @model_validator(mode="after")
    def _check_roles(self) -> "SignalApiSpec":
        unknown = sorted(set(self.field_map) - set(SIGNAL_FIELD_ROLES))
        if unknown:
            raise ValueError(f"signal_api.field_map 에 모르는 역할이 있습니다: {', '.join(unknown)}")
        return self


class CollectTargets(_Frozen):
    poll_s: float = Field(default=30.0, ge=10)
    routes: tuple[TargetRoute, ...]
    bike_areas: tuple[TargetArea, ...] = ()
    signal_areas: tuple[TargetArea, ...] = ()
    windows: tuple[DemoWindow, ...] = Field(min_length=1)
    holidays: tuple[str, ...] = ()
    daily_call_limits: dict[str, int] = {}  # API 이름 → 하루 한도
    bike_history: BikeHistorySpec
    signal_api: SignalApiSpec = SignalApiSpec()

    @model_validator(mode="after")
    def _check_targets(self) -> "CollectTargets":
        for day in self.holidays:
            _check_date(day, "휴일")
        bad = sorted(name for name, limit in self.daily_call_limits.items() if limit <= 0)
        if bad:
            raise ValueError(f"daily_call_limits 의 한도는 0 보다 커야 합니다: {', '.join(bad)}")
        return self


class ModelSummary(_Frozen):
    """화면 ⑦ 탭에 보이는 학습 모델 요약."""

    kind: Literal["SIGNAL", "BIKE"]
    path: str
    created_at: str
    period: str
    targets: NonNegInt
    rows: NonNegInt
    notes: tuple[str, ...] = ()


# ===== 지하철 시각표 스키마 (§4.10) =====


class TimetableRow(_Frozen):
    line: NonEmptyStr
    station: str
    direction: NonEmptyStr  # 상행, 하행, 내선, 외선
    day_type: DayType  # 그 열차가 다니는 운행일의 요일 종류
    train_no: NonEmptyStr
    arrive_s: float | None = Field(default=None, ge=0, lt=TWO_DAYS_S)  # 운행일 0시부터의 초
    depart_s: float | None = Field(default=None, ge=0, lt=TWO_DAYS_S)
    destination: str = ""
    express: bool = False

    @model_validator(mode="after")
    def _check_times(self) -> "TimetableRow":
        if self.arrive_s is None and self.depart_s is None:
            raise ValueError(f"열차 {self.train_no}: 도착과 출발 시각이 모두 없습니다")
        if self.arrive_s is not None and self.depart_s is not None and self.arrive_s > self.depart_s:
            raise ValueError(f"열차 {self.train_no}: 도착이 출발보다 늦습니다")
        return self


class Timetable(_Frozen):
    station_key: NonEmptyStr  # 역코드, 파일 이름과 같다
    rows: tuple[TimetableRow, ...] = Field(min_length=1)  # (요일 종류, 방향, 시각, 열차 번호) 순
    source: str  # 읽은 파일 이름과 수정 날짜

    @model_validator(mode="after")
    def _check_rows(self) -> "Timetable":
        seen: set[tuple] = set()
        for row in self.rows:
            key = (row.day_type, row.direction, row.train_no, row.arrive_s, row.depart_s)
            if key in seen:
                raise ValueError(f"역 {self.station_key}: 같은 행이 두 번 있습니다 (열차 {row.train_no})")
            seen.add(key)
        return self


class TrainChoice(_Frozen):
    """화면의 "지금 탄 열차" 후보(§4.10)."""

    station_key: str
    pattern_id: str
    trip_id: str
    index: NonNegInt  # 그 역의 순번 j_0
    train_no: str
    line: str
    direction: str
    destination: str
    express: bool
    arrive_s: float  # t = 0 기준, 그 역 도착
    clock_label: str  # 화면용 "HH:MM:SS"


# ===== 생성 명세 스키마 (§4.9) =====


class SpecPlace(_Frozen):
    name: NonEmptyStr
    lat: Latitude
    lon: Longitude


class SpecStationLine(_Frozen):
    line: NonEmptyStr
    lat: Latitude  # 승강장 좌표
    lon: Longitude
    stairs_m: PositiveFloat  # 승강장 ↔ 대합실
    key: str | None = None  # 그 호선의 역코드가 역 key 와 다를 때(환승역)


class SpecStationExit(_Frozen):
    name: NonEmptyStr
    lat: Latitude
    lon: Longitude
    passage_m: PositiveFloat  # 대합실 ↔ 출구


class SpecStationTransfer(_Frozen):
    lines: tuple[NonEmptyStr, NonEmptyStr]
    passage_m: PositiveFloat  # 두 승강장 사이


class SpecStation(_Frozen):
    key: NonEmptyStr  # 역코드
    name: str
    lines: tuple[SpecStationLine, ...] = Field(min_length=1)
    exits: tuple[SpecStationExit, ...] = ()
    transfers: tuple[SpecStationTransfer, ...] = ()

    @model_validator(mode="after")
    def _check_station(self) -> "SpecStation":
        names = [item.line for item in self.lines]
        dup = _duplicates(names)
        if dup:
            raise ValueError(f"역 {self.key}: 같은 호선이 둘 있습니다: {', '.join(dup)}")
        for item in self.lines:
            if item.key is not None and not item.key.strip():
                raise ValueError(f"역 {self.key}: 호선 {item.line} 의 key 가 비었습니다")
        for transfer in self.transfers:
            a, b = transfer.lines
            if a == b or a not in names or b not in names:
                raise ValueError(f"역 {self.key}: 환승 통로의 호선 ({a}, {b}) 는 이 역의 서로 다른 두 호선이어야 합니다")
        return self


class ScenarioBuildSpec(_Frozen):
    """생성 명세 `data/scenarios/<id>.spec.json` (§4.9)."""

    id: NonEmptyStr
    title: str
    description: str = ""
    bbox: tuple[float, float, float, float]  # 남, 서, 북, 동 (WGS84)
    places: tuple[SpecPlace, ...] = Field(min_length=2)  # 첫 둘이 기본 질의의 출발과 목적지
    route_ids: tuple[NonEmptyStr, ...] = ()
    stations: tuple[SpecStation, ...] = ()
    osm_file: NonEmptyStr  # 상대 경로면 데이터 폴더 기준
    clock: str  # "HH:MM:SS"
    day_type: DayType = DayType.WEEKDAY
    design_cycle_s: PositiveFloat = 150.0
    design_green_s: PositiveFloat = 30.0
    signal_map: tuple[tuple[int | str, str, str], ...] = ()  # (OSM 노드 ID, 신호 원천 ID, 방향 문구)
    map_zoom: int = Field(default=16, ge=1, le=20)

    @model_validator(mode="after")
    def _check_spec(self) -> "ScenarioBuildSpec":
        south, west, north, east = self.bbox
        if not (-90 <= south < north <= 90 and -180 <= west < east <= 180):
            raise ValueError("bbox 는 [남, 서, 북, 동] 이고 남 < 북, 서 < 동이어야 합니다")
        parts = self.clock.split(":")
        if len(parts) != 3 or not all(len(part) == 2 and part.isdigit() for part in parts):
            raise ValueError(f"clock {self.clock!r} 는 HH:MM:SS 형식이어야 합니다")
        hours, minutes, seconds = (int(part) for part in parts)
        if hours >= 24 or minutes >= 60 or seconds >= 60:
            raise ValueError(f"clock {self.clock!r} 는 00:00:00 ~ 23:59:59 여야 합니다")
        if self.design_green_s >= self.design_cycle_s:
            raise ValueError("design_green_s 는 design_cycle_s 보다 작아야 합니다")
        dup = _duplicates([station.key for station in self.stations])
        if dup:
            raise ValueError(f"stations 에 같은 역코드가 둘 있습니다: {', '.join(dup)}")
        dup = _duplicates([str(item[0]) for item in self.signal_map])
        if dup:
            raise ValueError(f"signal_map 에 같은 OSM 노드가 둘 있습니다: {', '.join(dup)}")
        dup = _duplicates(list(self.route_ids))
        if dup:
            raise ValueError(f"route_ids 에 같은 노선이 둘 있습니다: {', '.join(dup)}")
        return self

    @property
    def clock_s(self) -> float:
        hours, minutes, seconds = (int(part) for part in self.clock.split(":"))
        return float(hours * 3600 + minutes * 60 + seconds)
