-- Prove2me | Definitions.Def_Yukon_3b3a235dce6f52b341b88b39
-- name    : Yukon_3b3a235dce6f52b341b88b39
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:05:54.560979+00:00
-- url     : https://prove2.me/theorems/577dbbb1-46d7-4eb2-8fb8-aad5e863f832
-- title:
--   Relative certificate source part 5/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_3b3a235dce6f52b341b88b39
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGU3MDI1NDVmOWQzMjk0MmIxNGI0MGMyY2FkZWZkZjNjNzE5ZTYyMDM1MTYxZThhZmQ2OGQ1M2E4OTE1Y2M1MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fM2IzYTIzNWRjZTZmNTJiMzQxYjg4YjM5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fM2IzYTIzNWRjZTZmNTJiMzQxYjg4YjM5IiwidiI6Mn0]

import Definitions.Def_Yukon_31f07acb57a8a8d5ca2bbbda
import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_5a41472b766ae83852cae05b











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 260bcf0650f7b5b3a615c929dc34473a82a4248f4336de3d1583e250ba65488d.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b108 : List (Rectangle × FastWitness) := [(r864,⟨70,43,43⟩),(r865,⟨70,43,43⟩),(r866,⟨70,43,43⟩),(r867,⟨70,43,43⟩),(r868,⟨70,43,43⟩),(r869,⟨70,43,43⟩),(r870,⟨70,43,43⟩),(r871,⟨70,43,43⟩)]
theorem checked108 : fastCheckList band b108=true := by decide +kernel

def b109 : List (Rectangle × FastWitness) := [(r872,⟨70,43,43⟩),(r873,⟨70,43,43⟩),(r874,⟨70,43,43⟩),(r875,⟨70,43,43⟩),(r876,⟨70,43,43⟩),(r877,⟨70,43,43⟩),(r878,⟨70,43,43⟩),(r879,⟨70,43,43⟩)]
theorem checked109 : fastCheckList band b109=true := by decide +kernel

def b110 : List (Rectangle × FastWitness) := [(r880,⟨70,43,43⟩),(r881,⟨70,43,43⟩),(r882,⟨70,43,43⟩),(r883,⟨70,43,43⟩),(r884,⟨70,43,43⟩),(r885,⟨70,43,43⟩),(r886,⟨70,43,43⟩),(r887,⟨70,43,43⟩)]
theorem checked110 : fastCheckList band b110=true := by decide +kernel

def b111 : List (Rectangle × FastWitness) := [(r888,⟨70,43,43⟩),(r889,⟨70,43,43⟩),(r890,⟨70,43,43⟩),(r891,⟨70,43,43⟩),(r892,⟨70,43,43⟩),(r893,⟨70,43,43⟩),(r894,⟨70,43,43⟩),(r895,⟨70,43,43⟩)]
theorem checked111 : fastCheckList band b111=true := by decide +kernel

def b112 : List (Rectangle × FastWitness) := [(r896,⟨70,43,43⟩),(r897,⟨70,43,43⟩),(r898,⟨70,43,43⟩),(r899,⟨70,43,43⟩),(r900,⟨70,43,43⟩),(r901,⟨70,43,43⟩),(r902,⟨70,43,43⟩),(r903,⟨70,43,43⟩)]
theorem checked112 : fastCheckList band b112=true := by decide +kernel

def b113 : List (Rectangle × FastWitness) := [(r904,⟨70,43,43⟩),(r905,⟨70,43,43⟩),(r906,⟨70,43,43⟩),(r907,⟨70,43,43⟩),(r908,⟨70,43,43⟩),(r909,⟨70,43,43⟩),(r910,⟨70,43,43⟩),(r911,⟨70,43,43⟩)]
theorem checked113 : fastCheckList band b113=true := by decide +kernel

def b114 : List (Rectangle × FastWitness) := [(r912,⟨70,43,43⟩),(r913,⟨70,43,43⟩),(r914,⟨70,43,43⟩),(r915,⟨70,43,43⟩),(r916,⟨70,43,43⟩),(r917,⟨70,43,43⟩),(r918,⟨70,43,43⟩),(r919,⟨70,43,43⟩)]
theorem checked114 : fastCheckList band b114=true := by decide +kernel

def b115 : List (Rectangle × FastWitness) := [(r920,⟨70,43,43⟩),(r921,⟨70,43,43⟩),(r922,⟨70,43,43⟩),(r923,⟨70,43,43⟩),(r924,⟨70,43,43⟩),(r925,⟨70,43,43⟩),(r926,⟨70,43,43⟩),(r927,⟨70,43,43⟩)]
theorem checked115 : fastCheckList band b115=true := by decide +kernel

def b116 : List (Rectangle × FastWitness) := [(r928,⟨70,43,43⟩),(r929,⟨70,43,43⟩),(r930,⟨70,43,43⟩),(r931,⟨70,43,43⟩),(r932,⟨70,43,43⟩),(r933,⟨70,43,43⟩),(r934,⟨70,43,43⟩),(r935,⟨70,43,43⟩)]
theorem checked116 : fastCheckList band b116=true := by decide +kernel

def b117 : List (Rectangle × FastWitness) := [(r936,⟨70,43,43⟩),(r937,⟨70,43,43⟩),(r938,⟨70,43,43⟩),(r939,⟨70,43,43⟩),(r940,⟨70,43,43⟩),(r941,⟨70,43,43⟩),(r942,⟨70,43,43⟩),(r943,⟨70,43,43⟩)]
theorem checked117 : fastCheckList band b117=true := by decide +kernel

def b118 : List (Rectangle × FastWitness) := [(r944,⟨70,43,43⟩),(r945,⟨70,43,43⟩),(r946,⟨70,43,43⟩),(r947,⟨70,43,43⟩),(r948,⟨70,43,43⟩),(r949,⟨70,43,43⟩),(r950,⟨70,43,43⟩),(r951,⟨70,43,43⟩)]
theorem checked118 : fastCheckList band b118=true := by decide +kernel

def b119 : List (Rectangle × FastWitness) := [(r952,⟨70,43,43⟩),(r953,⟨70,43,43⟩),(r954,⟨70,43,43⟩),(r955,⟨70,43,43⟩),(r956,⟨70,43,43⟩),(r957,⟨70,43,43⟩),(r958,⟨70,43,43⟩),(r959,⟨70,43,43⟩)]
theorem checked119 : fastCheckList band b119=true := by decide +kernel

def b120 : List (Rectangle × FastWitness) := [(r960,⟨70,43,43⟩),(r961,⟨70,43,43⟩),(r962,⟨70,43,43⟩),(r963,⟨70,43,43⟩),(r964,⟨70,43,43⟩),(r965,⟨70,43,43⟩),(r966,⟨70,43,43⟩),(r967,⟨70,43,43⟩)]
theorem checked120 : fastCheckList band b120=true := by decide +kernel

def b121 : List (Rectangle × FastWitness) := [(r968,⟨70,43,43⟩),(r969,⟨70,43,43⟩),(r970,⟨70,43,43⟩),(r971,⟨70,43,43⟩),(r972,⟨70,43,43⟩),(r973,⟨70,43,43⟩),(r974,⟨70,43,43⟩),(r975,⟨70,43,43⟩)]
theorem checked121 : fastCheckList band b121=true := by decide +kernel

def b122 : List (Rectangle × FastWitness) := [(r976,⟨70,43,43⟩),(r977,⟨70,43,43⟩),(r978,⟨70,43,43⟩),(r979,⟨70,43,43⟩),(r980,⟨70,43,43⟩),(r981,⟨70,43,43⟩),(r982,⟨70,43,43⟩),(r983,⟨70,43,43⟩)]
theorem checked122 : fastCheckList band b122=true := by decide +kernel

def b123 : List (Rectangle × FastWitness) := [(r984,⟨70,43,43⟩),(r985,⟨70,43,43⟩),(r986,⟨70,43,43⟩),(r987,⟨70,43,43⟩),(r988,⟨70,43,43⟩),(r989,⟨70,43,43⟩),(r990,⟨70,43,43⟩),(r991,⟨70,43,43⟩)]
theorem checked123 : fastCheckList band b123=true := by decide +kernel

def b124 : List (Rectangle × FastWitness) := [(r992,⟨70,43,43⟩),(r993,⟨70,43,43⟩),(r994,⟨70,43,43⟩),(r995,⟨70,43,43⟩),(r996,⟨70,43,43⟩),(r997,⟨70,43,43⟩),(r998,⟨70,43,43⟩),(r999,⟨70,43,43⟩)]
theorem checked124 : fastCheckList band b124=true := by decide +kernel

def b125 : List (Rectangle × FastWitness) := [(r1000,⟨70,43,43⟩),(r1001,⟨70,43,43⟩),(r1002,⟨70,43,43⟩),(r1003,⟨70,43,43⟩),(r1004,⟨70,43,43⟩),(r1005,⟨70,43,43⟩),(r1006,⟨70,43,43⟩),(r1007,⟨70,43,43⟩)]
theorem checked125 : fastCheckList band b125=true := by decide +kernel

def b126 : List (Rectangle × FastWitness) := [(r1008,⟨70,43,43⟩),(r1009,⟨70,43,43⟩),(r1010,⟨70,43,43⟩),(r1011,⟨70,43,43⟩),(r1012,⟨70,43,43⟩),(r1013,⟨70,43,43⟩),(r1014,⟨70,43,43⟩),(r1015,⟨70,43,43⟩)]
theorem checked126 : fastCheckList band b126=true := by decide +kernel

def b127 : List (Rectangle × FastWitness) := [(r1016,⟨70,43,43⟩),(r1017,⟨70,43,43⟩),(r1018,⟨70,43,43⟩),(r1019,⟨70,43,43⟩),(r1020,⟨70,43,43⟩),(r1021,⟨70,43,43⟩),(r1022,⟨70,43,43⟩),(r1023,⟨70,43,43⟩)]
theorem checked127 : fastCheckList band b127=true := by decide +kernel

def b128 : List (Rectangle × FastWitness) := [(r1024,⟨70,43,43⟩),(r1025,⟨70,43,43⟩),(r1026,⟨70,43,43⟩),(r1027,⟨70,43,43⟩),(r1028,⟨70,43,43⟩),(r1029,⟨70,43,43⟩),(r1030,⟨70,43,43⟩),(r1031,⟨70,43,43⟩)]
theorem checked128 : fastCheckList band b128=true := by decide +kernel

def b129 : List (Rectangle × FastWitness) := [(r1032,⟨70,43,43⟩),(r1033,⟨70,43,43⟩),(r1034,⟨70,43,43⟩),(r1035,⟨70,43,43⟩),(r1036,⟨70,43,43⟩),(r1037,⟨70,43,43⟩),(r1038,⟨70,43,43⟩),(r1039,⟨70,43,43⟩)]
theorem checked129 : fastCheckList band b129=true := by decide +kernel

def b130 : List (Rectangle × FastWitness) := [(r1040,⟨70,43,43⟩),(r1041,⟨70,43,43⟩),(r1042,⟨70,43,43⟩),(r1043,⟨70,43,43⟩),(r1044,⟨70,43,43⟩),(r1045,⟨70,43,43⟩),(r1046,⟨70,43,43⟩),(r1047,⟨70,43,43⟩)]
theorem checked130 : fastCheckList band b130=true := by decide +kernel

def b131 : List (Rectangle × FastWitness) := [(r1048,⟨70,43,43⟩),(r1049,⟨70,43,43⟩),(r1050,⟨70,43,43⟩),(r1051,⟨70,43,43⟩),(r1052,⟨70,43,43⟩),(r1053,⟨70,43,43⟩),(r1054,⟨70,43,43⟩),(r1055,⟨70,43,43⟩)]
theorem checked131 : fastCheckList band b131=true := by decide +kernel

def b132 : List (Rectangle × FastWitness) := [(r1056,⟨70,43,43⟩),(r1057,⟨70,43,43⟩),(r1058,⟨70,43,43⟩),(r1059,⟨70,43,43⟩),(r1060,⟨70,43,43⟩),(r1061,⟨70,43,43⟩),(r1062,⟨70,43,43⟩),(r1063,⟨70,43,43⟩)]
theorem checked132 : fastCheckList band b132=true := by decide +kernel

def b133 : List (Rectangle × FastWitness) := [(r1064,⟨70,43,43⟩),(r1065,⟨70,43,43⟩),(r1066,⟨70,43,43⟩),(r1067,⟨70,43,43⟩),(r1068,⟨70,44,44⟩),(r1069,⟨70,44,44⟩),(r1070,⟨70,44,44⟩),(r1071,⟨70,44,44⟩)]
theorem checked133 : fastCheckList band b133=true := by decide +kernel

def b134 : List (Rectangle × FastWitness) := [(r1072,⟨70,44,44⟩),(r1073,⟨70,44,44⟩),(r1074,⟨70,44,44⟩),(r1075,⟨70,44,44⟩),(r1076,⟨70,44,44⟩),(r1077,⟨70,44,44⟩),(r1078,⟨70,44,44⟩),(r1079,⟨70,44,44⟩)]
theorem checked134 : fastCheckList band b134=true := by decide +kernel

def b135 : List (Rectangle × FastWitness) := [(r1080,⟨70,44,44⟩),(r1081,⟨70,44,44⟩),(r1082,⟨70,44,44⟩),(r1083,⟨70,44,44⟩),(r1084,⟨70,44,44⟩),(r1085,⟨70,44,44⟩),(r1086,⟨70,44,44⟩),(r1087,⟨70,44,44⟩)]
theorem checked135 : fastCheckList band b135=true := by decide +kernel

def b136 : List (Rectangle × FastWitness) := [(r1088,⟨70,44,44⟩),(r1089,⟨70,44,44⟩),(r1090,⟨70,44,44⟩),(r1091,⟨70,44,44⟩),(r1092,⟨70,44,44⟩),(r1093,⟨70,44,44⟩),(r1094,⟨70,44,44⟩),(r1095,⟨70,44,44⟩)]
theorem checked136 : fastCheckList band b136=true := by decide +kernel

def b137 : List (Rectangle × FastWitness) := [(r1096,⟨70,44,44⟩),(r1097,⟨70,44,44⟩),(r1098,⟨70,44,44⟩),(r1099,⟨70,44,44⟩),(r1100,⟨70,44,44⟩),(r1101,⟨70,44,44⟩),(r1102,⟨70,44,44⟩),(r1103,⟨70,44,44⟩)]
theorem checked137 : fastCheckList band b137=true := by decide +kernel

def b138 : List (Rectangle × FastWitness) := [(r1104,⟨70,44,44⟩),(r1105,⟨70,44,44⟩),(r1106,⟨70,44,44⟩),(r1107,⟨70,44,44⟩),(r1108,⟨70,44,44⟩),(r1109,⟨70,44,44⟩),(r1110,⟨70,44,44⟩),(r1111,⟨70,44,44⟩)]
theorem checked138 : fastCheckList band b138=true := by decide +kernel

def b139 : List (Rectangle × FastWitness) := [(r1112,⟨70,44,44⟩),(r1113,⟨70,44,44⟩),(r1114,⟨70,44,44⟩),(r1115,⟨70,44,44⟩),(r1116,⟨70,44,44⟩),(r1117,⟨70,44,44⟩),(r1118,⟨70,44,44⟩),(r1119,⟨70,44,44⟩)]
theorem checked139 : fastCheckList band b139=true := by decide +kernel

def b140 : List (Rectangle × FastWitness) := [(r1120,⟨70,44,44⟩),(r1121,⟨70,44,44⟩),(r1122,⟨70,44,44⟩),(r1123,⟨70,44,44⟩),(r1124,⟨70,44,44⟩),(r1125,⟨70,44,44⟩),(r1126,⟨70,44,44⟩),(r1127,⟨70,44,44⟩)]
theorem checked140 : fastCheckList band b140=true := by decide +kernel

def b141 : List (Rectangle × FastWitness) := [(r1128,⟨70,44,44⟩),(r1129,⟨70,44,44⟩),(r1130,⟨70,44,44⟩),(r1131,⟨70,44,44⟩),(r1132,⟨70,44,44⟩),(r1133,⟨70,44,44⟩),(r1134,⟨70,44,44⟩),(r1135,⟨70,44,44⟩)]
theorem checked141 : fastCheckList band b141=true := by decide +kernel

def b142 : List (Rectangle × FastWitness) := [(r1136,⟨70,44,44⟩),(r1137,⟨70,44,44⟩),(r1138,⟨70,44,44⟩),(r1139,⟨70,44,44⟩),(r1140,⟨70,44,44⟩),(r1141,⟨70,44,44⟩),(r1142,⟨70,44,44⟩),(r1143,⟨70,44,44⟩)]
theorem checked142 : fastCheckList band b142=true := by decide +kernel

def b143 : List (Rectangle × FastWitness) := [(r1144,⟨70,44,44⟩),(r1145,⟨70,44,44⟩),(r1146,⟨70,44,44⟩),(r1147,⟨70,44,44⟩),(r1148,⟨70,44,44⟩),(r1149,⟨70,44,44⟩),(r1150,⟨70,44,44⟩),(r1151,⟨70,44,44⟩)]
theorem checked143 : fastCheckList band b143=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


