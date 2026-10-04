-- Prove2me | Definitions.Def_Yukon_9b3f405663022c6a538954cc
-- name    : Yukon_9b3f405663022c6a538954cc
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:43:25.466587+00:00
-- url     : https://prove2.me/theorems/32089b2e-c753-4cbd-8e7c-aea1df71a456
-- title:
--   Relative certificate source part 6/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_9b3f405663022c6a538954cc
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjEyYWRiMjZmMTc2Y2Y0NDAzNTMwMzcxYWRmOTYyMmM2OTZkNjdmODFjZDljNjYxNzE2YzUxMjdjM2FmYjg1NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uXzliM2Y0MDU2NjMwMjJjNmE1Mzg5NTRjYyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzliM2Y0MDU2NjMwMjJjNmE1Mzg5NTRjYyIsInYiOjJ9]

import Definitions.Def_Yukon_93f639d3938205e1e2162e83
import Definitions.Def_Yukon_e757298719adf05c20287f89












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: c5a3d79401563549e3da246da1fa707d32f52f28e1c561a2e007749bd764d43f.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b128 : List (Rectangle × FastWitness) := [(r1024,⟨67,40,40⟩),(r1025,⟨67,40,40⟩),(r1026,⟨67,40,40⟩),(r1027,⟨67,40,40⟩),(r1028,⟨67,40,40⟩),(r1029,⟨67,40,40⟩),(r1030,⟨67,40,40⟩),(r1031,⟨67,40,40⟩)]
theorem checked128 : fastCheckList band b128=true := by decide +kernel

def b129 : List (Rectangle × FastWitness) := [(r1032,⟨67,40,40⟩),(r1033,⟨67,40,40⟩),(r1034,⟨67,40,40⟩),(r1035,⟨67,40,40⟩),(r1036,⟨67,40,40⟩),(r1037,⟨67,40,40⟩),(r1038,⟨67,40,40⟩),(r1039,⟨67,40,40⟩)]
theorem checked129 : fastCheckList band b129=true := by decide +kernel

def b130 : List (Rectangle × FastWitness) := [(r1040,⟨67,40,40⟩),(r1041,⟨67,40,40⟩),(r1042,⟨67,40,40⟩),(r1043,⟨67,40,40⟩),(r1044,⟨67,40,40⟩),(r1045,⟨67,40,40⟩),(r1046,⟨67,40,40⟩),(r1047,⟨67,40,40⟩)]
theorem checked130 : fastCheckList band b130=true := by decide +kernel

def b131 : List (Rectangle × FastWitness) := [(r1048,⟨67,40,40⟩),(r1049,⟨67,40,40⟩),(r1050,⟨67,40,40⟩),(r1051,⟨67,40,40⟩),(r1052,⟨67,40,40⟩),(r1053,⟨67,40,40⟩),(r1054,⟨67,40,40⟩),(r1055,⟨67,40,40⟩)]
theorem checked131 : fastCheckList band b131=true := by decide +kernel

def b132 : List (Rectangle × FastWitness) := [(r1056,⟨67,40,40⟩),(r1057,⟨67,40,40⟩),(r1058,⟨67,40,40⟩),(r1059,⟨67,40,40⟩),(r1060,⟨67,40,40⟩),(r1061,⟨67,40,40⟩),(r1062,⟨67,40,40⟩),(r1063,⟨67,40,40⟩)]
theorem checked132 : fastCheckList band b132=true := by decide +kernel

def b133 : List (Rectangle × FastWitness) := [(r1064,⟨67,40,40⟩),(r1065,⟨67,40,40⟩),(r1066,⟨67,40,40⟩),(r1067,⟨67,40,40⟩),(r1068,⟨67,40,40⟩),(r1069,⟨67,40,40⟩),(r1070,⟨67,40,40⟩),(r1071,⟨67,40,40⟩)]
theorem checked133 : fastCheckList band b133=true := by decide +kernel

def b134 : List (Rectangle × FastWitness) := [(r1072,⟨67,40,40⟩),(r1073,⟨67,40,40⟩),(r1074,⟨67,40,40⟩),(r1075,⟨67,40,40⟩),(r1076,⟨67,40,40⟩),(r1077,⟨67,40,40⟩),(r1078,⟨67,40,40⟩),(r1079,⟨67,40,40⟩)]
theorem checked134 : fastCheckList band b134=true := by decide +kernel

def b135 : List (Rectangle × FastWitness) := [(r1080,⟨67,40,40⟩),(r1081,⟨67,40,40⟩),(r1082,⟨67,40,40⟩),(r1083,⟨67,40,40⟩),(r1084,⟨67,40,40⟩),(r1085,⟨67,40,40⟩),(r1086,⟨67,40,40⟩),(r1087,⟨67,40,40⟩)]
theorem checked135 : fastCheckList band b135=true := by decide +kernel

def b136 : List (Rectangle × FastWitness) := [(r1088,⟨67,40,40⟩),(r1089,⟨67,40,40⟩),(r1090,⟨67,40,40⟩),(r1091,⟨67,40,40⟩),(r1092,⟨67,40,40⟩),(r1093,⟨67,40,40⟩),(r1094,⟨67,40,40⟩),(r1095,⟨67,40,40⟩)]
theorem checked136 : fastCheckList band b136=true := by decide +kernel

def b137 : List (Rectangle × FastWitness) := [(r1096,⟨67,40,40⟩),(r1097,⟨67,40,40⟩),(r1098,⟨67,40,40⟩),(r1099,⟨67,40,40⟩),(r1100,⟨67,40,40⟩),(r1101,⟨67,40,40⟩),(r1102,⟨67,40,40⟩),(r1103,⟨67,40,40⟩)]
theorem checked137 : fastCheckList band b137=true := by decide +kernel

def b138 : List (Rectangle × FastWitness) := [(r1104,⟨67,40,40⟩),(r1105,⟨67,40,40⟩),(r1106,⟨67,40,40⟩),(r1107,⟨67,40,40⟩),(r1108,⟨67,40,40⟩),(r1109,⟨67,40,40⟩),(r1110,⟨67,40,40⟩),(r1111,⟨67,40,40⟩)]
theorem checked138 : fastCheckList band b138=true := by decide +kernel

def b139 : List (Rectangle × FastWitness) := [(r1112,⟨67,40,40⟩),(r1113,⟨67,40,40⟩),(r1114,⟨67,40,40⟩),(r1115,⟨67,40,40⟩),(r1116,⟨67,40,40⟩),(r1117,⟨67,40,40⟩),(r1118,⟨67,40,40⟩),(r1119,⟨67,40,40⟩)]
theorem checked139 : fastCheckList band b139=true := by decide +kernel

def b140 : List (Rectangle × FastWitness) := [(r1120,⟨67,40,40⟩),(r1121,⟨67,40,40⟩),(r1122,⟨67,40,40⟩),(r1123,⟨67,40,40⟩),(r1124,⟨67,40,40⟩),(r1125,⟨67,40,40⟩),(r1126,⟨67,40,40⟩),(r1127,⟨67,40,40⟩)]
theorem checked140 : fastCheckList band b140=true := by decide +kernel

def b141 : List (Rectangle × FastWitness) := [(r1128,⟨67,40,40⟩),(r1129,⟨67,40,40⟩),(r1130,⟨67,40,40⟩),(r1131,⟨67,40,40⟩),(r1132,⟨67,40,40⟩),(r1133,⟨67,40,40⟩),(r1134,⟨67,40,40⟩),(r1135,⟨67,40,40⟩)]
theorem checked141 : fastCheckList band b141=true := by decide +kernel

def b142 : List (Rectangle × FastWitness) := [(r1136,⟨67,40,40⟩),(r1137,⟨67,40,40⟩),(r1138,⟨67,40,40⟩),(r1139,⟨67,40,40⟩),(r1140,⟨67,40,40⟩),(r1141,⟨67,40,40⟩),(r1142,⟨67,40,40⟩),(r1143,⟨67,40,40⟩)]
theorem checked142 : fastCheckList band b142=true := by decide +kernel

def b143 : List (Rectangle × FastWitness) := [(r1144,⟨67,40,40⟩),(r1145,⟨67,40,40⟩),(r1146,⟨67,40,40⟩),(r1147,⟨67,40,40⟩),(r1148,⟨67,40,40⟩),(r1149,⟨67,40,40⟩),(r1150,⟨67,40,40⟩),(r1151,⟨67,40,40⟩)]
theorem checked143 : fastCheckList band b143=true := by decide +kernel

def b144 : List (Rectangle × FastWitness) := [(r1152,⟨67,40,40⟩),(r1153,⟨67,40,40⟩),(r1154,⟨67,40,40⟩),(r1155,⟨67,40,40⟩),(r1156,⟨67,40,40⟩),(r1157,⟨67,40,40⟩),(r1158,⟨67,40,40⟩),(r1159,⟨67,40,40⟩)]
theorem checked144 : fastCheckList band b144=true := by decide +kernel

def b145 : List (Rectangle × FastWitness) := [(r1160,⟨67,40,40⟩),(r1161,⟨67,40,40⟩),(r1162,⟨67,40,40⟩),(r1163,⟨67,40,40⟩),(r1164,⟨67,40,40⟩),(r1165,⟨67,40,40⟩),(r1166,⟨67,40,40⟩),(r1167,⟨67,40,40⟩)]
theorem checked145 : fastCheckList band b145=true := by decide +kernel

def b146 : List (Rectangle × FastWitness) := [(r1168,⟨67,40,40⟩),(r1169,⟨67,40,40⟩),(r1170,⟨67,40,40⟩),(r1171,⟨67,40,40⟩),(r1172,⟨67,40,40⟩),(r1173,⟨67,40,40⟩),(r1174,⟨67,40,40⟩),(r1175,⟨67,40,40⟩)]
theorem checked146 : fastCheckList band b146=true := by decide +kernel

def b147 : List (Rectangle × FastWitness) := [(r1176,⟨67,40,40⟩),(r1177,⟨67,40,40⟩),(r1178,⟨67,40,40⟩),(r1179,⟨67,40,40⟩),(r1180,⟨67,40,40⟩),(r1181,⟨67,40,40⟩),(r1182,⟨67,40,40⟩),(r1183,⟨67,40,40⟩)]
theorem checked147 : fastCheckList band b147=true := by decide +kernel

def b148 : List (Rectangle × FastWitness) := [(r1184,⟨67,40,40⟩),(r1185,⟨67,40,40⟩),(r1186,⟨67,40,40⟩),(r1187,⟨67,40,40⟩),(r1188,⟨67,40,40⟩),(r1189,⟨67,40,40⟩),(r1190,⟨67,40,40⟩),(r1191,⟨67,40,40⟩)]
theorem checked148 : fastCheckList band b148=true := by decide +kernel

def b149 : List (Rectangle × FastWitness) := [(r1192,⟨67,40,40⟩),(r1193,⟨67,40,40⟩),(r1194,⟨67,40,40⟩),(r1195,⟨67,40,40⟩),(r1196,⟨67,40,40⟩),(r1197,⟨67,40,40⟩),(r1198,⟨67,40,40⟩),(r1199,⟨67,40,40⟩)]
theorem checked149 : fastCheckList band b149=true := by decide +kernel

def b150 : List (Rectangle × FastWitness) := [(r1200,⟨67,40,40⟩),(r1201,⟨67,40,40⟩),(r1202,⟨67,40,40⟩),(r1203,⟨67,40,40⟩),(r1204,⟨67,40,40⟩),(r1205,⟨67,40,40⟩),(r1206,⟨67,40,40⟩),(r1207,⟨67,40,40⟩)]
theorem checked150 : fastCheckList band b150=true := by decide +kernel

def b151 : List (Rectangle × FastWitness) := [(r1208,⟨67,40,40⟩),(r1209,⟨67,40,40⟩),(r1210,⟨67,40,40⟩),(r1211,⟨67,40,40⟩),(r1212,⟨67,40,40⟩),(r1213,⟨67,40,40⟩),(r1214,⟨67,40,40⟩),(r1215,⟨67,40,40⟩)]
theorem checked151 : fastCheckList band b151=true := by decide +kernel

def b152 : List (Rectangle × FastWitness) := [(r1216,⟨67,40,40⟩),(r1217,⟨67,40,40⟩),(r1218,⟨67,40,40⟩),(r1219,⟨67,40,40⟩),(r1220,⟨67,40,40⟩),(r1221,⟨67,40,40⟩),(r1222,⟨67,40,40⟩),(r1223,⟨67,40,40⟩)]
theorem checked152 : fastCheckList band b152=true := by decide +kernel

def b153 : List (Rectangle × FastWitness) := [(r1224,⟨67,40,40⟩),(r1225,⟨67,40,40⟩),(r1226,⟨67,40,40⟩),(r1227,⟨67,40,40⟩),(r1228,⟨67,40,40⟩),(r1229,⟨67,40,40⟩),(r1230,⟨67,40,40⟩),(r1231,⟨67,40,40⟩)]
theorem checked153 : fastCheckList band b153=true := by decide +kernel

def b154 : List (Rectangle × FastWitness) := [(r1232,⟨67,40,40⟩),(r1233,⟨67,40,40⟩),(r1234,⟨67,40,40⟩),(r1235,⟨67,40,40⟩),(r1236,⟨67,40,40⟩),(r1237,⟨67,40,40⟩),(r1238,⟨67,40,40⟩),(r1239,⟨67,40,40⟩)]
theorem checked154 : fastCheckList band b154=true := by decide +kernel

def b155 : List (Rectangle × FastWitness) := [(r1240,⟨67,40,40⟩),(r1241,⟨67,40,40⟩),(r1242,⟨67,40,40⟩),(r1243,⟨67,40,40⟩),(r1244,⟨67,40,40⟩),(r1245,⟨67,40,40⟩),(r1246,⟨67,40,40⟩),(r1247,⟨67,40,40⟩)]
theorem checked155 : fastCheckList band b155=true := by decide +kernel

def b156 : List (Rectangle × FastWitness) := [(r1248,⟨67,40,40⟩),(r1249,⟨67,40,40⟩),(r1250,⟨67,40,40⟩),(r1251,⟨67,40,40⟩),(r1252,⟨67,40,40⟩),(r1253,⟨67,40,40⟩),(r1254,⟨67,40,40⟩),(r1255,⟨67,40,40⟩)]
theorem checked156 : fastCheckList band b156=true := by decide +kernel

def b157 : List (Rectangle × FastWitness) := [(r1256,⟨67,40,40⟩),(r1257,⟨67,40,40⟩),(r1258,⟨67,40,40⟩),(r1259,⟨67,40,40⟩),(r1260,⟨67,40,40⟩),(r1261,⟨67,40,40⟩),(r1262,⟨67,40,40⟩),(r1263,⟨67,40,40⟩)]
theorem checked157 : fastCheckList band b157=true := by decide +kernel

def b158 : List (Rectangle × FastWitness) := [(r1264,⟨67,40,40⟩),(r1265,⟨67,40,40⟩),(r1266,⟨67,40,40⟩),(r1267,⟨67,40,41⟩),(r1268,⟨67,40,40⟩),(r1269,⟨67,40,40⟩),(r1270,⟨67,40,41⟩),(r1271,⟨67,40,40⟩)]
theorem checked158 : fastCheckList band b158=true := by decide +kernel

def b159 : List (Rectangle × FastWitness) := [(r1272,⟨67,40,40⟩),(r1273,⟨67,40,40⟩),(r1274,⟨67,40,40⟩),(r1275,⟨67,40,40⟩),(r1276,⟨67,40,40⟩),(r1277,⟨67,40,40⟩),(r1278,⟨67,40,40⟩),(r1279,⟨67,40,40⟩)]
theorem checked159 : fastCheckList band b159=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


