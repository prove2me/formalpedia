-- Prove2me | Definitions.Def_Yukon_fb2407a3a15551029023b1a5
-- name    : Yukon_fb2407a3a15551029023b1a5
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:06:58.171038+00:00
-- url     : https://prove2.me/theorems/227258f4-62f6-477b-91b6-964ee24aa857
-- title:
--   Relative certificate source part 6/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_fb2407a3a15551029023b1a5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjdiMmFhNTM3MTYyZTU1ZmNkNDkwOTBhMzQyZDlmZDhiYmQ4MDkzMGJjYTdkMjBlMzQ4NDYyMzJjZGE3NDUyZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fZmIyNDA3YTNhMTU1NTEwMjkwMjNiMWE1IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fZmIyNDA3YTNhMTU1NTEwMjkwMjNiMWE1IiwidiI6Mn0]

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

def b144 : List (Rectangle × FastWitness) := [(r1152,⟨70,44,44⟩),(r1153,⟨70,44,44⟩),(r1154,⟨70,44,44⟩),(r1155,⟨70,44,44⟩),(r1156,⟨70,44,44⟩),(r1157,⟨70,44,44⟩),(r1158,⟨70,44,44⟩),(r1159,⟨70,44,44⟩)]
theorem checked144 : fastCheckList band b144=true := by decide +kernel

def b145 : List (Rectangle × FastWitness) := [(r1160,⟨70,44,44⟩),(r1161,⟨70,44,44⟩),(r1162,⟨70,44,44⟩),(r1163,⟨70,44,44⟩),(r1164,⟨70,44,44⟩),(r1165,⟨70,44,44⟩),(r1166,⟨70,44,44⟩),(r1167,⟨70,44,44⟩)]
theorem checked145 : fastCheckList band b145=true := by decide +kernel

def b146 : List (Rectangle × FastWitness) := [(r1168,⟨70,44,44⟩),(r1169,⟨70,44,44⟩),(r1170,⟨70,44,44⟩),(r1171,⟨70,44,44⟩),(r1172,⟨70,44,44⟩),(r1173,⟨70,44,44⟩),(r1174,⟨70,44,44⟩),(r1175,⟨70,44,44⟩)]
theorem checked146 : fastCheckList band b146=true := by decide +kernel

def b147 : List (Rectangle × FastWitness) := [(r1176,⟨70,44,44⟩),(r1177,⟨70,44,44⟩),(r1178,⟨70,44,44⟩),(r1179,⟨70,44,44⟩),(r1180,⟨70,44,44⟩),(r1181,⟨70,44,44⟩),(r1182,⟨70,44,44⟩),(r1183,⟨70,44,44⟩)]
theorem checked147 : fastCheckList band b147=true := by decide +kernel

def b148 : List (Rectangle × FastWitness) := [(r1184,⟨70,44,44⟩),(r1185,⟨70,44,44⟩),(r1186,⟨70,44,44⟩),(r1187,⟨70,44,44⟩),(r1188,⟨70,44,44⟩),(r1189,⟨70,44,44⟩),(r1190,⟨70,44,44⟩),(r1191,⟨70,44,44⟩)]
theorem checked148 : fastCheckList band b148=true := by decide +kernel

def b149 : List (Rectangle × FastWitness) := [(r1192,⟨70,44,44⟩),(r1193,⟨70,44,44⟩),(r1194,⟨70,44,44⟩),(r1195,⟨70,44,44⟩),(r1196,⟨70,44,44⟩),(r1197,⟨70,44,44⟩),(r1198,⟨70,44,44⟩),(r1199,⟨70,44,44⟩)]
theorem checked149 : fastCheckList band b149=true := by decide +kernel

def b150 : List (Rectangle × FastWitness) := [(r1200,⟨70,44,44⟩),(r1201,⟨70,44,44⟩),(r1202,⟨70,44,44⟩),(r1203,⟨70,44,44⟩),(r1204,⟨70,44,44⟩),(r1205,⟨70,44,44⟩),(r1206,⟨70,44,44⟩),(r1207,⟨70,44,44⟩)]
theorem checked150 : fastCheckList band b150=true := by decide +kernel

def b151 : List (Rectangle × FastWitness) := [(r1208,⟨70,45,45⟩),(r1209,⟨70,45,45⟩),(r1210,⟨70,45,45⟩),(r1211,⟨70,45,45⟩),(r1212,⟨70,45,45⟩),(r1213,⟨70,45,45⟩),(r1214,⟨70,45,45⟩),(r1215,⟨70,45,45⟩)]
theorem checked151 : fastCheckList band b151=true := by decide +kernel

def b152 : List (Rectangle × FastWitness) := [(r1216,⟨70,45,45⟩),(r1217,⟨70,45,45⟩),(r1218,⟨70,45,45⟩),(r1219,⟨70,45,45⟩),(r1220,⟨70,45,45⟩),(r1221,⟨70,45,45⟩),(r1222,⟨70,45,45⟩),(r1223,⟨70,45,45⟩)]
theorem checked152 : fastCheckList band b152=true := by decide +kernel

def b153 : List (Rectangle × FastWitness) := [(r1224,⟨70,45,45⟩),(r1225,⟨70,45,45⟩),(r1226,⟨70,45,45⟩),(r1227,⟨70,45,45⟩),(r1228,⟨70,45,45⟩),(r1229,⟨70,45,45⟩),(r1230,⟨70,45,45⟩),(r1231,⟨70,45,45⟩)]
theorem checked153 : fastCheckList band b153=true := by decide +kernel

def b154 : List (Rectangle × FastWitness) := [(r1232,⟨70,45,45⟩),(r1233,⟨70,45,45⟩),(r1234,⟨70,45,45⟩),(r1235,⟨70,45,45⟩),(r1236,⟨70,45,45⟩),(r1237,⟨70,45,45⟩),(r1238,⟨70,45,45⟩),(r1239,⟨70,45,45⟩)]
theorem checked154 : fastCheckList band b154=true := by decide +kernel

def b155 : List (Rectangle × FastWitness) := [(r1240,⟨70,45,45⟩),(r1241,⟨70,45,45⟩),(r1242,⟨70,45,45⟩),(r1243,⟨70,45,45⟩),(r1244,⟨70,45,45⟩),(r1245,⟨70,45,45⟩),(r1246,⟨70,45,45⟩),(r1247,⟨70,45,45⟩)]
theorem checked155 : fastCheckList band b155=true := by decide +kernel

def b156 : List (Rectangle × FastWitness) := [(r1248,⟨70,45,45⟩),(r1249,⟨70,45,45⟩),(r1250,⟨70,45,45⟩),(r1251,⟨70,45,45⟩),(r1252,⟨70,45,45⟩),(r1253,⟨70,45,45⟩),(r1254,⟨70,45,45⟩),(r1255,⟨70,45,45⟩)]
theorem checked156 : fastCheckList band b156=true := by decide +kernel

def b157 : List (Rectangle × FastWitness) := [(r1256,⟨70,45,45⟩),(r1257,⟨70,45,45⟩),(r1258,⟨70,45,45⟩),(r1259,⟨70,45,45⟩),(r1260,⟨70,45,45⟩),(r1261,⟨70,45,45⟩),(r1262,⟨70,45,45⟩),(r1263,⟨70,45,45⟩)]
theorem checked157 : fastCheckList band b157=true := by decide +kernel

def b158 : List (Rectangle × FastWitness) := [(r1264,⟨70,45,45⟩),(r1265,⟨70,45,45⟩),(r1266,⟨70,45,45⟩),(r1267,⟨70,45,45⟩),(r1268,⟨70,45,45⟩),(r1269,⟨70,45,45⟩),(r1270,⟨70,45,45⟩),(r1271,⟨70,45,45⟩)]
theorem checked158 : fastCheckList band b158=true := by decide +kernel

def b159 : List (Rectangle × FastWitness) := [(r1272,⟨70,45,45⟩),(r1273,⟨70,45,45⟩),(r1274,⟨70,45,45⟩),(r1275,⟨70,45,45⟩),(r1276,⟨70,45,45⟩),(r1277,⟨70,45,45⟩),(r1278,⟨70,45,45⟩),(r1279,⟨70,45,45⟩)]
theorem checked159 : fastCheckList band b159=true := by decide +kernel

def b160 : List (Rectangle × FastWitness) := [(r1280,⟨70,45,45⟩),(r1281,⟨70,45,45⟩),(r1282,⟨70,45,45⟩),(r1283,⟨70,45,45⟩),(r1284,⟨70,45,45⟩),(r1285,⟨70,45,45⟩),(r1286,⟨70,45,46⟩),(r1287,⟨70,45,46⟩)]
theorem checked160 : fastCheckList band b160=true := by decide +kernel

def b161 : List (Rectangle × FastWitness) := [(r1288,⟨70,45,46⟩),(r1289,⟨70,45,46⟩),(r1290,⟨70,45,46⟩),(r1291,⟨70,45,46⟩),(r1292,⟨70,45,46⟩),(r1293,⟨70,45,46⟩),(r1294,⟨70,45,46⟩),(r1295,⟨70,45,46⟩)]
theorem checked161 : fastCheckList band b161=true := by decide +kernel

def b162 : List (Rectangle × FastWitness) := [(r1296,⟨70,45,46⟩),(r1297,⟨70,45,46⟩),(r1298,⟨70,45,46⟩),(r1299,⟨70,45,46⟩),(r1300,⟨70,45,46⟩),(r1301,⟨70,45,46⟩),(r1302,⟨70,45,46⟩),(r1303,⟨70,45,46⟩)]
theorem checked162 : fastCheckList band b162=true := by decide +kernel

def b163 : List (Rectangle × FastWitness) := [(r1304,⟨70,45,46⟩),(r1305,⟨70,46,46⟩),(r1306,⟨70,46,46⟩),(r1307,⟨70,46,46⟩),(r1308,⟨70,46,46⟩),(r1309,⟨70,46,46⟩),(r1310,⟨70,46,46⟩),(r1311,⟨70,46,46⟩)]
theorem checked163 : fastCheckList band b163=true := by decide +kernel

def b164 : List (Rectangle × FastWitness) := [(r1312,⟨70,46,46⟩),(r1313,⟨70,46,46⟩),(r1314,⟨70,46,46⟩),(r1315,⟨70,46,46⟩),(r1316,⟨70,46,46⟩),(r1317,⟨70,45,46⟩),(r1318,⟨70,45,46⟩),(r1319,⟨70,45,46⟩)]
theorem checked164 : fastCheckList band b164=true := by decide +kernel

def b165 : List (Rectangle × FastWitness) := [(r1320,⟨70,45,46⟩),(r1321,⟨70,45,46⟩),(r1322,⟨70,45,46⟩),(r1323,⟨70,45,46⟩),(r1324,⟨70,45,46⟩),(r1325,⟨70,45,46⟩),(r1326,⟨70,45,46⟩),(r1327,⟨70,45,46⟩)]
theorem checked165 : fastCheckList band b165=true := by decide +kernel

def b166 : List (Rectangle × FastWitness) := [(r1328,⟨70,45,46⟩),(r1329,⟨70,45,46⟩),(r1330,⟨70,45,46⟩),(r1331,⟨70,45,46⟩),(r1332,⟨70,45,46⟩),(r1333,⟨70,45,46⟩),(r1334,⟨70,45,46⟩),(r1335,⟨70,45,46⟩)]
theorem checked166 : fastCheckList band b166=true := by decide +kernel

def b167 : List (Rectangle × FastWitness) := [(r1336,⟨70,45,46⟩),(r1337,⟨70,45,46⟩),(r1338,⟨70,45,46⟩),(r1339,⟨70,45,46⟩),(r1340,⟨70,45,46⟩),(r1341,⟨70,45,46⟩),(r1342,⟨70,45,46⟩),(r1343,⟨70,45,46⟩)]
theorem checked167 : fastCheckList band b167=true := by decide +kernel

def b168 : List (Rectangle × FastWitness) := [(r1344,⟨70,45,46⟩),(r1345,⟨70,45,46⟩),(r1346,⟨70,45,46⟩),(r1347,⟨70,45,46⟩),(r1348,⟨70,45,46⟩),(r1349,⟨70,45,46⟩),(r1350,⟨70,45,46⟩),(r1351,⟨70,45,46⟩)]
theorem checked168 : fastCheckList band b168=true := by decide +kernel

def b169 : List (Rectangle × FastWitness) := [(r1352,⟨70,45,46⟩),(r1353,⟨70,45,46⟩),(r1354,⟨70,45,46⟩),(r1355,⟨70,45,46⟩),(r1356,⟨70,45,46⟩),(r1357,⟨70,45,46⟩),(r1358,⟨70,45,46⟩),(r1359,⟨70,45,46⟩)]
theorem checked169 : fastCheckList band b169=true := by decide +kernel

def b170 : List (Rectangle × FastWitness) := [(r1360,⟨70,45,46⟩),(r1361,⟨70,45,46⟩),(r1362,⟨70,45,46⟩),(r1363,⟨70,45,46⟩),(r1364,⟨70,46,46⟩),(r1365,⟨70,46,46⟩),(r1366,⟨70,46,46⟩),(r1367,⟨70,46,46⟩)]
theorem checked170 : fastCheckList band b170=true := by decide +kernel

def b171 : List (Rectangle × FastWitness) := [(r1368,⟨70,46,46⟩),(r1369,⟨70,46,46⟩),(r1370,⟨70,46,46⟩),(r1371,⟨70,46,46⟩),(r1372,⟨70,46,46⟩),(r1373,⟨70,46,46⟩),(r1374,⟨70,46,46⟩),(r1375,⟨70,46,46⟩)]
theorem checked171 : fastCheckList band b171=true := by decide +kernel

def b172 : List (Rectangle × FastWitness) := [(r1376,⟨70,46,46⟩),(r1377,⟨70,46,46⟩),(r1378,⟨70,46,46⟩),(r1379,⟨70,46,46⟩),(r1380,⟨70,46,46⟩),(r1381,⟨70,46,46⟩),(r1382,⟨70,46,46⟩),(r1383,⟨70,46,46⟩)]
theorem checked172 : fastCheckList band b172=true := by decide +kernel

def b173 : List (Rectangle × FastWitness) := [(r1384,⟨70,46,46⟩),(r1385,⟨70,46,46⟩),(r1386,⟨70,46,46⟩),(r1387,⟨70,46,46⟩),(r1388,⟨70,46,46⟩),(r1389,⟨70,46,46⟩),(r1390,⟨70,46,46⟩),(r1391,⟨70,46,46⟩)]
theorem checked173 : fastCheckList band b173=true := by decide +kernel

def b174 : List (Rectangle × FastWitness) := [(r1392,⟨70,46,46⟩),(r1393,⟨70,46,46⟩),(r1394,⟨70,46,46⟩),(r1395,⟨70,46,46⟩),(r1396,⟨70,46,46⟩),(r1397,⟨70,46,46⟩),(r1398,⟨70,46,46⟩),(r1399,⟨70,46,46⟩)]
theorem checked174 : fastCheckList band b174=true := by decide +kernel

def b175 : List (Rectangle × FastWitness) := [(r1400,⟨70,46,46⟩),(r1401,⟨70,46,46⟩),(r1402,⟨70,46,46⟩),(r1403,⟨70,46,46⟩),(r1404,⟨70,46,46⟩),(r1405,⟨70,46,46⟩),(r1406,⟨70,46,46⟩),(r1407,⟨70,46,46⟩)]
theorem checked175 : fastCheckList band b175=true := by decide +kernel

def b176 : List (Rectangle × FastWitness) := [(r1408,⟨70,47,47⟩),(r1409,⟨70,47,47⟩),(r1410,⟨70,47,47⟩),(r1411,⟨70,47,47⟩),(r1412,⟨70,47,47⟩),(r1413,⟨70,47,47⟩),(r1414,⟨70,47,47⟩),(r1415,⟨70,47,47⟩)]
theorem checked176 : fastCheckList band b176=true := by decide +kernel

def b177 : List (Rectangle × FastWitness) := [(r1416,⟨70,47,47⟩),(r1417,⟨70,47,47⟩),(r1418,⟨70,47,47⟩),(r1419,⟨70,47,47⟩),(r1420,⟨70,47,47⟩),(r1421,⟨70,47,47⟩),(r1422,⟨70,47,47⟩),(r1423,⟨70,47,47⟩)]
theorem checked177 : fastCheckList band b177=true := by decide +kernel

def b178 : List (Rectangle × FastWitness) := [(r1424,⟨70,47,47⟩),(r1425,⟨70,47,48⟩),(r1426,⟨70,47,48⟩),(r1427,⟨70,47,48⟩),(r1428,⟨70,47,48⟩),(r1429,⟨70,47,48⟩),(r1430,⟨70,47,48⟩),(r1431,⟨70,47,48⟩)]
theorem checked178 : fastCheckList band b178=true := by decide +kernel

def b179 : List (Rectangle × FastWitness) := [(r1432,⟨70,47,48⟩),(r1433,⟨70,47,48⟩),(r1434,⟨70,47,48⟩),(r1435,⟨70,47,48⟩),(r1436,⟨70,47,48⟩),(r1437,⟨70,47,48⟩),(r1438,⟨70,47,48⟩),(r1439,⟨70,47,48⟩)]
theorem checked179 : fastCheckList band b179=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


