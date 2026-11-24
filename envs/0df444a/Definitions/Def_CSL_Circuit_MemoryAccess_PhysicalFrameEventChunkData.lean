-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
-- name    : CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:16:35.798452+00:00
-- url     : https://prove2.me/theorems/50c14a07-45fa-4c22-97fa-b57695f38644
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFrameEventChunkData
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventChunkData` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventChunkData

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventProperties

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
universe u

def forwardEventChunk000 : List FrameEvent := gatesChunk0.toList.map ordinaryEvent
def forwardEventChunk001 : List FrameEvent := gatesChunk1.toList.map ordinaryEvent
def forwardEventChunk002 : List FrameEvent := gatesChunk2.toList.map ordinaryEvent
def forwardEventChunk003 : List FrameEvent := gatesChunk3.toList.map ordinaryEvent
def forwardEventChunk004 : List FrameEvent := gatesChunk4.toList.map ordinaryEvent
def forwardEventChunk005 : List FrameEvent := gatesChunk5.toList.map ordinaryEvent
def forwardEventChunk006 : List FrameEvent := gatesChunk6.toList.map ordinaryEvent
def forwardEventChunk007 : List FrameEvent := gatesChunk7.toList.map ordinaryEvent
def forwardEventChunk008 : List FrameEvent := gatesChunk8.toList.map ordinaryEvent
def forwardEventChunk009 : List FrameEvent := gatesChunk9.toList.map ordinaryEvent
def forwardEventChunk010 : List FrameEvent := gatesChunk10.toList.map ordinaryEvent
def forwardEventChunk011 : List FrameEvent := gatesChunk11.toList.map ordinaryEvent
def forwardEventChunk012 : List FrameEvent := gatesChunk12.toList.map ordinaryEvent
def forwardEventChunk013 : List FrameEvent := gatesChunk13.toList.map ordinaryEvent
def forwardEventChunk014 : List FrameEvent := gatesChunk14.toList.map ordinaryEvent
def forwardEventChunk015 : List FrameEvent := gatesChunk15.toList.map ordinaryEvent
def forwardEventChunk016 : List FrameEvent := gatesChunk16.toList.map ordinaryEvent
def forwardEventChunk017 : List FrameEvent := gatesChunk17.toList.map ordinaryEvent
def forwardEventChunk018 : List FrameEvent := gatesChunk18.toList.map ordinaryEvent
def forwardEventChunk019 : List FrameEvent := gatesChunk19.toList.map ordinaryEvent
def forwardEventChunk020 : List FrameEvent := gatesChunk20.toList.map ordinaryEvent
def forwardEventChunk021 : List FrameEvent := gatesChunk21.toList.map ordinaryEvent
def forwardEventChunk022 : List FrameEvent := gatesChunk22.toList.map ordinaryEvent
def forwardEventChunk023 : List FrameEvent := gatesChunk23.toList.map ordinaryEvent
def forwardEventChunk024 : List FrameEvent := gatesChunk24.toList.map ordinaryEvent
def forwardEventChunk025 : List FrameEvent := gatesChunk25.toList.map ordinaryEvent
def forwardEventChunk026 : List FrameEvent := gatesChunk26.toList.map ordinaryEvent
def forwardEventChunk027 : List FrameEvent := gatesChunk27.toList.map ordinaryEvent
def forwardEventChunk028 : List FrameEvent := gatesChunk28.toList.map ordinaryEvent
def forwardEventChunk029 : List FrameEvent := gatesChunk29.toList.map ordinaryEvent
def forwardEventChunk030 : List FrameEvent := gatesChunk30.toList.map ordinaryEvent
def forwardEventChunk031 : List FrameEvent := gatesChunk31.toList.map ordinaryEvent
def forwardEventChunk032 : List FrameEvent := gatesChunk32.toList.map ordinaryEvent
def forwardEventChunk033 : List FrameEvent := gatesChunk33.toList.map ordinaryEvent
def forwardEventChunk034 : List FrameEvent := gatesChunk34.toList.map ordinaryEvent
def forwardEventChunk035 : List FrameEvent := gatesChunk35.toList.map ordinaryEvent
def forwardEventChunk036 : List FrameEvent := gatesChunk36.toList.map ordinaryEvent
def forwardEventChunk037 : List FrameEvent := gatesChunk37.toList.map ordinaryEvent
def forwardEventChunk038 : List FrameEvent := gatesChunk38.toList.map ordinaryEvent
def forwardEventChunk039 : List FrameEvent := gatesChunk39.toList.map ordinaryEvent
def forwardEventChunk040 : List FrameEvent := gatesChunk40.toList.map ordinaryEvent
def forwardEventChunk041 : List FrameEvent := gatesChunk41.toList.map ordinaryEvent
def forwardEventChunk042 : List FrameEvent := gatesChunk42.toList.map ordinaryEvent
def forwardEventChunk043 : List FrameEvent := gatesChunk43.toList.map ordinaryEvent
def forwardEventChunk044 : List FrameEvent := gatesChunk44.toList.map ordinaryEvent
def forwardEventChunk045 : List FrameEvent := gatesChunk45.toList.map ordinaryEvent
def forwardEventChunk046 : List FrameEvent := gatesChunk46.toList.map ordinaryEvent
def forwardEventChunk047 : List FrameEvent := gatesChunk47.toList.map ordinaryEvent
def forwardEventChunk048 : List FrameEvent := gatesChunk48.toList.map ordinaryEvent
def forwardEventChunk049 : List FrameEvent := gatesChunk49.toList.map ordinaryEvent
def forwardEventChunk050 : List FrameEvent := gatesChunk50.toList.map ordinaryEvent
def forwardEventChunk051 : List FrameEvent := gatesChunk51.toList.map ordinaryEvent
def forwardEventChunk052 : List FrameEvent := gatesChunk52.toList.map ordinaryEvent
def forwardEventChunk053 : List FrameEvent := gatesChunk53.toList.map ordinaryEvent
def forwardEventChunk054 : List FrameEvent := gatesChunk54.toList.map ordinaryEvent
def forwardEventChunk055 : List FrameEvent := gatesChunk55.toList.map ordinaryEvent
def forwardEventChunk056 : List FrameEvent := gatesChunk56.toList.map ordinaryEvent
def forwardEventChunk057 : List FrameEvent := gatesChunk57.toList.map ordinaryEvent
def forwardEventChunk058 : List FrameEvent := gatesChunk58.toList.map ordinaryEvent
def forwardEventChunk059 : List FrameEvent := gatesChunk59.toList.map ordinaryEvent
def forwardEventChunk060 : List FrameEvent := gatesChunk60.toList.map ordinaryEvent
def forwardEventChunk061 : List FrameEvent := gatesChunk61.toList.map ordinaryEvent
def forwardEventChunk062 : List FrameEvent := gatesChunk62.toList.map ordinaryEvent
def forwardEventChunk063 : List FrameEvent := gatesChunk63.toList.map ordinaryEvent
def forwardEventChunk064 : List FrameEvent := gatesChunk64.toList.map ordinaryEvent
def forwardEventChunk065 : List FrameEvent := gatesChunk65.toList.map ordinaryEvent
def forwardEventChunk066 : List FrameEvent := gatesChunk66.toList.map ordinaryEvent
def forwardEventChunk067 : List FrameEvent := gatesChunk67.toList.map ordinaryEvent
def forwardEventChunk068 : List FrameEvent := (gatesChunk68.toList.take 10).map ordinaryEvent
def forwardEventChunk069 : List FrameEvent := (List.range 9).map copyEvent
def forwardEventChunk070 : List FrameEvent := (gatesChunk68.toList.drop 10).map scatterEvent
def forwardEventChunk071 : List FrameEvent := gatesChunk69.toList.map scatterEvent
def forwardEventChunk072 : List FrameEvent := gatesChunk70.toList.map scatterEvent
def forwardEventChunk073 : List FrameEvent := (gatesChunk71.toList.take 25).map scatterEvent
def forwardEventChunk074 : List FrameEvent := (gatesChunk71.toList.drop 25).map ordinaryEvent
def forwardEventChunk075 : List FrameEvent := gatesChunk72.toList.map ordinaryEvent
def forwardEventChunk076 : List FrameEvent := gatesChunk73.toList.map ordinaryEvent
def forwardEventChunk077 : List FrameEvent := gatesChunk74.toList.map ordinaryEvent
def forwardEventChunk078 : List FrameEvent := gatesChunk75.toList.map ordinaryEvent
def forwardEventChunk079 : List FrameEvent := gatesChunk76.toList.map ordinaryEvent
def forwardEventChunk080 : List FrameEvent := gatesChunk77.toList.map ordinaryEvent
def forwardEventChunk081 : List FrameEvent := gatesChunk78.toList.map ordinaryEvent
def forwardEventChunk082 : List FrameEvent := gatesChunk79.toList.map ordinaryEvent
def forwardEventChunk083 : List FrameEvent := gatesChunk80.toList.map ordinaryEvent
def forwardEventChunk084 : List FrameEvent := gatesChunk81.toList.map ordinaryEvent
def forwardEventChunk085 : List FrameEvent := gatesChunk82.toList.map ordinaryEvent
def forwardEventChunk086 : List FrameEvent := gatesChunk83.toList.map ordinaryEvent
def forwardEventChunk087 : List FrameEvent := gatesChunk84.toList.map ordinaryEvent
def forwardEventChunk088 : List FrameEvent := gatesChunk85.toList.map ordinaryEvent
def forwardEventChunk089 : List FrameEvent := gatesChunk86.toList.map ordinaryEvent
def forwardEventChunk090 : List FrameEvent := gatesChunk87.toList.map ordinaryEvent
def forwardEventChunk091 : List FrameEvent := gatesChunk88.toList.map ordinaryEvent
def forwardEventChunk092 : List FrameEvent := gatesChunk89.toList.map ordinaryEvent
def forwardEventChunk093 : List FrameEvent := gatesChunk90.toList.map ordinaryEvent
def forwardEventChunk094 : List FrameEvent := gatesChunk91.toList.map ordinaryEvent
def forwardEventChunk095 : List FrameEvent := gatesChunk92.toList.map ordinaryEvent
def forwardEventChunk096 : List FrameEvent := gatesChunk93.toList.map ordinaryEvent
def forwardEventChunk097 : List FrameEvent := gatesChunk94.toList.map ordinaryEvent
def forwardEventChunk098 : List FrameEvent := gatesChunk95.toList.map ordinaryEvent
def forwardEventChunk099 : List FrameEvent := gatesChunk96.toList.map ordinaryEvent
def forwardEventChunk100 : List FrameEvent := gatesChunk97.toList.map ordinaryEvent
def forwardEventChunk101 : List FrameEvent := gatesChunk98.toList.map ordinaryEvent
def forwardEventChunk102 : List FrameEvent := gatesChunk99.toList.map ordinaryEvent
def forwardEventChunk103 : List FrameEvent := gatesChunk100.toList.map ordinaryEvent
def forwardEventChunk104 : List FrameEvent := gatesChunk101.toList.map ordinaryEvent
def forwardEventChunk105 : List FrameEvent := gatesChunk102.toList.map ordinaryEvent
def forwardEventChunk106 : List FrameEvent := gatesChunk103.toList.map ordinaryEvent
def forwardEventChunk107 : List FrameEvent := gatesChunk104.toList.map ordinaryEvent
def forwardEventChunk108 : List FrameEvent := gatesChunk105.toList.map ordinaryEvent
def forwardEventChunk109 : List FrameEvent := gatesChunk106.toList.map ordinaryEvent
def forwardEventChunk110 : List FrameEvent := gatesChunk107.toList.map ordinaryEvent
def forwardEventChunk111 : List FrameEvent := gatesChunk108.toList.map ordinaryEvent
def forwardEventChunk112 : List FrameEvent := gatesChunk109.toList.map ordinaryEvent
def forwardEventChunk113 : List FrameEvent := gatesChunk110.toList.map ordinaryEvent
def forwardEventChunk114 : List FrameEvent := gatesChunk111.toList.map ordinaryEvent
def forwardEventChunk115 : List FrameEvent := gatesChunk112.toList.map ordinaryEvent
def forwardEventChunk116 : List FrameEvent := gatesChunk113.toList.map ordinaryEvent
def forwardEventChunk117 : List FrameEvent := gatesChunk114.toList.map ordinaryEvent
def forwardEventChunk118 : List FrameEvent := gatesChunk115.toList.map ordinaryEvent
def forwardEventChunk119 : List FrameEvent := gatesChunk116.toList.map ordinaryEvent
def forwardEventChunk120 : List FrameEvent := gatesChunk117.toList.map ordinaryEvent
def forwardEventChunk121 : List FrameEvent := gatesChunk118.toList.map ordinaryEvent
def forwardEventChunk122 : List FrameEvent := gatesChunk119.toList.map ordinaryEvent
def forwardEventChunk123 : List FrameEvent := gatesChunk120.toList.map ordinaryEvent
def forwardEventChunk124 : List FrameEvent := gatesChunk121.toList.map ordinaryEvent
def forwardEventChunk125 : List FrameEvent := gatesChunk122.toList.map ordinaryEvent
def forwardEventChunk126 : List FrameEvent := gatesChunk123.toList.map ordinaryEvent
def forwardEventChunk127 : List FrameEvent := gatesChunk124.toList.map ordinaryEvent
def forwardEventChunk128 : List FrameEvent := gatesChunk125.toList.map ordinaryEvent
def forwardEventChunk129 : List FrameEvent := gatesChunk126.toList.map ordinaryEvent
def forwardEventChunk130 : List FrameEvent := gatesChunk127.toList.map ordinaryEvent
def forwardEventChunk131 : List FrameEvent := gatesChunk128.toList.map ordinaryEvent
def forwardEventChunk132 : List FrameEvent := gatesChunk129.toList.map ordinaryEvent
def forwardEventChunk133 : List FrameEvent := gatesChunk130.toList.map ordinaryEvent
def forwardEventChunk134 : List FrameEvent := gatesChunk131.toList.map ordinaryEvent
def forwardEventChunk135 : List FrameEvent := gatesChunk132.toList.map ordinaryEvent
def forwardEventChunk136 : List FrameEvent := gatesChunk133.toList.map ordinaryEvent
def forwardEventChunk137 : List FrameEvent := gatesChunk134.toList.map ordinaryEvent
def forwardEventChunk138 : List FrameEvent := gatesChunk135.toList.map ordinaryEvent
def forwardEventChunk139 : List FrameEvent := gatesChunk136.toList.map ordinaryEvent
def forwardEventChunk140 : List FrameEvent := gatesChunk137.toList.map ordinaryEvent
def forwardEventChunk141 : List FrameEvent := gatesChunk138.toList.map ordinaryEvent
def forwardEventChunk142 : List FrameEvent := gatesChunk139.toList.map ordinaryEvent
def forwardEventChunk143 : List FrameEvent := gatesChunk140.toList.map ordinaryEvent
def forwardEventChunk144 : List FrameEvent := gatesChunk141.toList.map ordinaryEvent
def forwardEventChunk145 : List FrameEvent := gatesChunk142.toList.map ordinaryEvent
def forwardEventChunk146 : List FrameEvent := gatesChunk143.toList.map ordinaryEvent
def forwardEventChunk147 : List FrameEvent := gatesChunk144.toList.map ordinaryEvent
def forwardEventChunk148 : List FrameEvent := gatesChunk145.toList.map ordinaryEvent
def forwardEventChunk149 : List FrameEvent := gatesChunk146.toList.map ordinaryEvent
def forwardEventChunk150 : List FrameEvent := gatesChunk147.toList.map ordinaryEvent
def forwardEventChunk151 : List FrameEvent := gatesChunk148.toList.map ordinaryEvent
def forwardEventChunk152 : List FrameEvent := gatesChunk149.toList.map ordinaryEvent
def forwardEventChunk153 : List FrameEvent := gatesChunk150.toList.map ordinaryEvent
def forwardEventChunk154 : List FrameEvent := gatesChunk151.toList.map ordinaryEvent
def forwardEventChunk155 : List FrameEvent := gatesChunk152.toList.map ordinaryEvent
def forwardEventChunk156 : List FrameEvent := gatesChunk153.toList.map ordinaryEvent
def forwardEventChunk157 : List FrameEvent := gatesChunk154.toList.map ordinaryEvent
def forwardEventChunk158 : List FrameEvent := gatesChunk155.toList.map ordinaryEvent
def forwardEventChunk159 : List FrameEvent := gatesChunk156.toList.map ordinaryEvent
def forwardEventChunk160 : List FrameEvent := gatesChunk157.toList.map ordinaryEvent
def forwardEventChunk161 : List FrameEvent := gatesChunk158.toList.map ordinaryEvent
def forwardEventChunk162 : List FrameEvent := gatesChunk159.toList.map ordinaryEvent
def forwardEventChunk163 : List FrameEvent := gatesChunk160.toList.map ordinaryEvent
def forwardEventChunk164 : List FrameEvent := gatesChunk161.toList.map ordinaryEvent
def forwardEventChunk165 : List FrameEvent := gatesChunk162.toList.map ordinaryEvent
def forwardEventChunk166 : List FrameEvent := gatesChunk163.toList.map ordinaryEvent
def forwardEventChunk167 : List FrameEvent := gatesChunk164.toList.map ordinaryEvent
def forwardEventChunk168 : List FrameEvent := gatesChunk165.toList.map ordinaryEvent
def forwardEventChunk169 : List FrameEvent := gatesChunk166.toList.map ordinaryEvent
def forwardEventChunk170 : List FrameEvent := gatesChunk167.toList.map ordinaryEvent
def forwardEventChunk171 : List FrameEvent := gatesChunk168.toList.map ordinaryEvent
def forwardEventChunk172 : List FrameEvent := gatesChunk169.toList.map ordinaryEvent
def forwardEventChunk173 : List FrameEvent := gatesChunk170.toList.map ordinaryEvent
def forwardEventChunk174 : List FrameEvent := gatesChunk171.toList.map ordinaryEvent
def forwardEventChunk175 : List FrameEvent := gatesChunk172.toList.map ordinaryEvent
def forwardEventChunk176 : List FrameEvent := gatesChunk173.toList.map ordinaryEvent
def forwardEventChunk177 : List FrameEvent := gatesChunk174.toList.map ordinaryEvent

def forwardEventChunks : List (List FrameEvent) := [
  forwardEventChunk000,
  forwardEventChunk001,
  forwardEventChunk002,
  forwardEventChunk003,
  forwardEventChunk004,
  forwardEventChunk005,
  forwardEventChunk006,
  forwardEventChunk007,
  forwardEventChunk008,
  forwardEventChunk009,
  forwardEventChunk010,
  forwardEventChunk011,
  forwardEventChunk012,
  forwardEventChunk013,
  forwardEventChunk014,
  forwardEventChunk015,
  forwardEventChunk016,
  forwardEventChunk017,
  forwardEventChunk018,
  forwardEventChunk019,
  forwardEventChunk020,
  forwardEventChunk021,
  forwardEventChunk022,
  forwardEventChunk023,
  forwardEventChunk024,
  forwardEventChunk025,
  forwardEventChunk026,
  forwardEventChunk027,
  forwardEventChunk028,
  forwardEventChunk029,
  forwardEventChunk030,
  forwardEventChunk031,
  forwardEventChunk032,
  forwardEventChunk033,
  forwardEventChunk034,
  forwardEventChunk035,
  forwardEventChunk036,
  forwardEventChunk037,
  forwardEventChunk038,
  forwardEventChunk039,
  forwardEventChunk040,
  forwardEventChunk041,
  forwardEventChunk042,
  forwardEventChunk043,
  forwardEventChunk044,
  forwardEventChunk045,
  forwardEventChunk046,
  forwardEventChunk047,
  forwardEventChunk048,
  forwardEventChunk049,
  forwardEventChunk050,
  forwardEventChunk051,
  forwardEventChunk052,
  forwardEventChunk053,
  forwardEventChunk054,
  forwardEventChunk055,
  forwardEventChunk056,
  forwardEventChunk057,
  forwardEventChunk058,
  forwardEventChunk059,
  forwardEventChunk060,
  forwardEventChunk061,
  forwardEventChunk062,
  forwardEventChunk063,
  forwardEventChunk064,
  forwardEventChunk065,
  forwardEventChunk066,
  forwardEventChunk067,
  forwardEventChunk068,
  forwardEventChunk069,
  forwardEventChunk070,
  forwardEventChunk071,
  forwardEventChunk072,
  forwardEventChunk073,
  forwardEventChunk074,
  forwardEventChunk075,
  forwardEventChunk076,
  forwardEventChunk077,
  forwardEventChunk078,
  forwardEventChunk079,
  forwardEventChunk080,
  forwardEventChunk081,
  forwardEventChunk082,
  forwardEventChunk083,
  forwardEventChunk084,
  forwardEventChunk085,
  forwardEventChunk086,
  forwardEventChunk087,
  forwardEventChunk088,
  forwardEventChunk089,
  forwardEventChunk090,
  forwardEventChunk091,
  forwardEventChunk092,
  forwardEventChunk093,
  forwardEventChunk094,
  forwardEventChunk095,
  forwardEventChunk096,
  forwardEventChunk097,
  forwardEventChunk098,
  forwardEventChunk099,
  forwardEventChunk100,
  forwardEventChunk101,
  forwardEventChunk102,
  forwardEventChunk103,
  forwardEventChunk104,
  forwardEventChunk105,
  forwardEventChunk106,
  forwardEventChunk107,
  forwardEventChunk108,
  forwardEventChunk109,
  forwardEventChunk110,
  forwardEventChunk111,
  forwardEventChunk112,
  forwardEventChunk113,
  forwardEventChunk114,
  forwardEventChunk115,
  forwardEventChunk116,
  forwardEventChunk117,
  forwardEventChunk118,
  forwardEventChunk119,
  forwardEventChunk120,
  forwardEventChunk121,
  forwardEventChunk122,
  forwardEventChunk123,
  forwardEventChunk124,
  forwardEventChunk125,
  forwardEventChunk126,
  forwardEventChunk127,
  forwardEventChunk128,
  forwardEventChunk129,
  forwardEventChunk130,
  forwardEventChunk131,
  forwardEventChunk132,
  forwardEventChunk133,
  forwardEventChunk134,
  forwardEventChunk135,
  forwardEventChunk136,
  forwardEventChunk137,
  forwardEventChunk138,
  forwardEventChunk139,
  forwardEventChunk140,
  forwardEventChunk141,
  forwardEventChunk142,
  forwardEventChunk143,
  forwardEventChunk144,
  forwardEventChunk145,
  forwardEventChunk146,
  forwardEventChunk147,
  forwardEventChunk148,
  forwardEventChunk149,
  forwardEventChunk150,
  forwardEventChunk151,
  forwardEventChunk152,
  forwardEventChunk153,
  forwardEventChunk154,
  forwardEventChunk155,
  forwardEventChunk156,
  forwardEventChunk157,
  forwardEventChunk158,
  forwardEventChunk159,
  forwardEventChunk160,
  forwardEventChunk161,
  forwardEventChunk162,
  forwardEventChunk163,
  forwardEventChunk164,
  forwardEventChunk165,
  forwardEventChunk166,
  forwardEventChunk167,
  forwardEventChunk168,
  forwardEventChunk169,
  forwardEventChunk170,
  forwardEventChunk171,
  forwardEventChunk172,
  forwardEventChunk173,
  forwardEventChunk174,
  forwardEventChunk175,
  forwardEventChunk176,
  forwardEventChunk177]

end CSL.Construction.PhysicalFramePaths


