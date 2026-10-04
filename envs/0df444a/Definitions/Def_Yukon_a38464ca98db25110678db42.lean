-- Prove2me | Definitions.Def_Yukon_a38464ca98db25110678db42
-- name    : Yukon_a38464ca98db25110678db42
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:43:04.002892+00:00
-- url     : https://prove2.me/theorems/b3698b10-0bab-4119-a676-9364a80e906e
-- title:
--   Relative certificate source part 7/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_a38464ca98db25110678db42
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjNkMzEyMmI1MjNiZWM5MjkwNTJjYzk2MTNlNDMyMDVkMjBhN2E1NzVjYzcyYWUwZGEzNzAzNjQ4YjVjN2M3NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2EzODQ2NGNhOThkYjI1MTEwNjc4ZGI0MiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2EzODQ2NGNhOThkYjI1MTEwNjc4ZGI0MiIsInYiOjJ9]

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

def b160 : List (Rectangle × FastWitness) := [(r1280,⟨67,40,40⟩),(r1281,⟨67,40,40⟩),(r1282,⟨67,40,40⟩),(r1283,⟨67,40,40⟩),(r1284,⟨67,40,40⟩),(r1285,⟨67,40,41⟩),(r1286,⟨67,40,40⟩),(r1287,⟨67,40,40⟩)]
theorem checked160 : fastCheckList band b160=true := by decide +kernel

def b161 : List (Rectangle × FastWitness) := [(r1288,⟨67,40,40⟩),(r1289,⟨67,40,40⟩),(r1290,⟨67,40,40⟩),(r1291,⟨67,40,40⟩),(r1292,⟨67,40,40⟩),(r1293,⟨67,40,40⟩),(r1294,⟨67,40,40⟩),(r1295,⟨67,40,40⟩)]
theorem checked161 : fastCheckList band b161=true := by decide +kernel

def b162 : List (Rectangle × FastWitness) := [(r1296,⟨67,40,40⟩),(r1297,⟨67,40,40⟩),(r1298,⟨67,40,40⟩),(r1299,⟨67,40,40⟩),(r1300,⟨67,40,40⟩),(r1301,⟨67,40,40⟩),(r1302,⟨67,40,40⟩),(r1303,⟨67,40,40⟩)]
theorem checked162 : fastCheckList band b162=true := by decide +kernel

def b163 : List (Rectangle × FastWitness) := [(r1304,⟨67,40,40⟩),(r1305,⟨67,40,40⟩),(r1306,⟨67,40,40⟩),(r1307,⟨67,40,40⟩),(r1308,⟨67,40,40⟩),(r1309,⟨67,40,40⟩),(r1310,⟨67,40,40⟩),(r1311,⟨67,40,40⟩)]
theorem checked163 : fastCheckList band b163=true := by decide +kernel

def b164 : List (Rectangle × FastWitness) := [(r1312,⟨67,40,40⟩),(r1313,⟨67,40,40⟩),(r1314,⟨67,40,40⟩),(r1315,⟨67,40,40⟩),(r1316,⟨67,40,40⟩),(r1317,⟨67,40,40⟩),(r1318,⟨67,40,40⟩),(r1319,⟨67,40,40⟩)]
theorem checked164 : fastCheckList band b164=true := by decide +kernel

def b165 : List (Rectangle × FastWitness) := [(r1320,⟨67,40,40⟩),(r1321,⟨67,40,40⟩),(r1322,⟨67,40,40⟩),(r1323,⟨67,40,40⟩),(r1324,⟨67,40,40⟩),(r1325,⟨67,40,40⟩),(r1326,⟨67,40,40⟩),(r1327,⟨67,40,40⟩)]
theorem checked165 : fastCheckList band b165=true := by decide +kernel

def b166 : List (Rectangle × FastWitness) := [(r1328,⟨67,40,40⟩),(r1329,⟨67,40,40⟩),(r1330,⟨67,40,40⟩),(r1331,⟨67,40,40⟩),(r1332,⟨67,40,40⟩),(r1333,⟨67,40,40⟩),(r1334,⟨67,40,40⟩),(r1335,⟨67,40,40⟩)]
theorem checked166 : fastCheckList band b166=true := by decide +kernel

def b167 : List (Rectangle × FastWitness) := [(r1336,⟨67,40,40⟩),(r1337,⟨67,40,40⟩),(r1338,⟨67,40,40⟩),(r1339,⟨67,40,40⟩),(r1340,⟨67,40,40⟩),(r1341,⟨67,40,40⟩),(r1342,⟨67,40,40⟩),(r1343,⟨67,40,40⟩)]
theorem checked167 : fastCheckList band b167=true := by decide +kernel

def b168 : List (Rectangle × FastWitness) := [(r1344,⟨67,40,40⟩),(r1345,⟨67,40,40⟩),(r1346,⟨67,40,40⟩),(r1347,⟨67,40,40⟩),(r1348,⟨67,40,40⟩),(r1349,⟨67,40,40⟩),(r1350,⟨67,40,40⟩),(r1351,⟨67,40,40⟩)]
theorem checked168 : fastCheckList band b168=true := by decide +kernel

def b169 : List (Rectangle × FastWitness) := [(r1352,⟨67,40,40⟩),(r1353,⟨67,40,40⟩),(r1354,⟨67,40,40⟩),(r1355,⟨67,40,40⟩),(r1356,⟨67,40,40⟩),(r1357,⟨67,40,40⟩),(r1358,⟨67,40,40⟩),(r1359,⟨67,40,40⟩)]
theorem checked169 : fastCheckList band b169=true := by decide +kernel

def b170 : List (Rectangle × FastWitness) := [(r1360,⟨67,40,40⟩),(r1361,⟨67,40,40⟩),(r1362,⟨67,40,41⟩),(r1363,⟨67,40,41⟩),(r1364,⟨67,40,41⟩),(r1365,⟨67,40,41⟩),(r1366,⟨67,40,41⟩),(r1367,⟨67,40,41⟩)]
theorem checked170 : fastCheckList band b170=true := by decide +kernel

def b171 : List (Rectangle × FastWitness) := [(r1368,⟨67,40,41⟩),(r1369,⟨67,40,41⟩),(r1370,⟨67,40,41⟩),(r1371,⟨67,40,41⟩),(r1372,⟨67,40,41⟩),(r1373,⟨67,40,41⟩),(r1374,⟨67,40,41⟩),(r1375,⟨67,40,41⟩)]
theorem checked171 : fastCheckList band b171=true := by decide +kernel

def b172 : List (Rectangle × FastWitness) := [(r1376,⟨67,40,41⟩),(r1377,⟨67,40,41⟩),(r1378,⟨67,41,41⟩),(r1379,⟨67,41,41⟩),(r1380,⟨67,41,41⟩),(r1381,⟨67,41,41⟩),(r1382,⟨67,41,41⟩),(r1383,⟨67,41,41⟩)]
theorem checked172 : fastCheckList band b172=true := by decide +kernel

def b173 : List (Rectangle × FastWitness) := [(r1384,⟨67,41,41⟩),(r1385,⟨67,41,41⟩),(r1386,⟨67,41,41⟩),(r1387,⟨67,41,41⟩),(r1388,⟨67,41,41⟩),(r1389,⟨67,41,41⟩),(r1390,⟨67,41,41⟩),(r1391,⟨67,41,41⟩)]
theorem checked173 : fastCheckList band b173=true := by decide +kernel

def b174 : List (Rectangle × FastWitness) := [(r1392,⟨67,41,41⟩),(r1393,⟨67,41,41⟩),(r1394,⟨67,41,41⟩),(r1395,⟨67,41,41⟩),(r1396,⟨67,41,41⟩),(r1397,⟨67,41,41⟩),(r1398,⟨67,41,41⟩),(r1399,⟨67,41,41⟩)]
theorem checked174 : fastCheckList band b174=true := by decide +kernel

def b175 : List (Rectangle × FastWitness) := [(r1400,⟨67,41,41⟩),(r1401,⟨67,41,41⟩),(r1402,⟨67,41,41⟩),(r1403,⟨67,41,41⟩),(r1404,⟨67,41,41⟩),(r1405,⟨67,41,41⟩),(r1406,⟨67,41,41⟩),(r1407,⟨67,41,41⟩)]
theorem checked175 : fastCheckList band b175=true := by decide +kernel

def b176 : List (Rectangle × FastWitness) := [(r1408,⟨67,41,41⟩),(r1409,⟨67,41,41⟩),(r1410,⟨67,41,41⟩),(r1411,⟨67,41,41⟩),(r1412,⟨67,41,41⟩),(r1413,⟨67,41,41⟩),(r1414,⟨67,41,41⟩),(r1415,⟨67,41,41⟩)]
theorem checked176 : fastCheckList band b176=true := by decide +kernel

def b177 : List (Rectangle × FastWitness) := [(r1416,⟨67,41,41⟩),(r1417,⟨67,41,41⟩),(r1418,⟨67,41,41⟩),(r1419,⟨67,41,41⟩),(r1420,⟨67,41,41⟩),(r1421,⟨67,41,41⟩),(r1422,⟨67,41,41⟩),(r1423,⟨67,41,41⟩)]
theorem checked177 : fastCheckList band b177=true := by decide +kernel

def b178 : List (Rectangle × FastWitness) := [(r1424,⟨67,41,41⟩),(r1425,⟨67,41,41⟩),(r1426,⟨67,41,41⟩),(r1427,⟨67,41,41⟩),(r1428,⟨67,41,41⟩),(r1429,⟨67,41,41⟩),(r1430,⟨67,41,41⟩),(r1431,⟨67,41,41⟩)]
theorem checked178 : fastCheckList band b178=true := by decide +kernel

def b179 : List (Rectangle × FastWitness) := [(r1432,⟨67,41,41⟩),(r1433,⟨67,41,41⟩),(r1434,⟨67,41,41⟩),(r1435,⟨67,41,41⟩),(r1436,⟨67,41,41⟩),(r1437,⟨67,41,41⟩),(r1438,⟨67,41,41⟩),(r1439,⟨67,41,41⟩)]
theorem checked179 : fastCheckList band b179=true := by decide +kernel

def b180 : List (Rectangle × FastWitness) := [(r1440,⟨67,41,41⟩),(r1441,⟨67,41,41⟩),(r1442,⟨67,41,41⟩),(r1443,⟨67,41,41⟩),(r1444,⟨67,41,41⟩),(r1445,⟨67,41,41⟩),(r1446,⟨67,41,41⟩),(r1447,⟨67,41,41⟩)]
theorem checked180 : fastCheckList band b180=true := by decide +kernel

def b181 : List (Rectangle × FastWitness) := [(r1448,⟨67,41,41⟩),(r1449,⟨67,41,41⟩),(r1450,⟨67,41,41⟩),(r1451,⟨67,41,41⟩),(r1452,⟨67,41,41⟩),(r1453,⟨67,41,41⟩),(r1454,⟨67,41,41⟩),(r1455,⟨67,41,41⟩)]
theorem checked181 : fastCheckList band b181=true := by decide +kernel

def b182 : List (Rectangle × FastWitness) := [(r1456,⟨67,41,41⟩),(r1457,⟨67,41,41⟩),(r1458,⟨67,41,41⟩),(r1459,⟨67,41,41⟩),(r1460,⟨67,41,41⟩),(r1461,⟨67,41,41⟩),(r1462,⟨67,41,41⟩),(r1463,⟨67,41,41⟩)]
theorem checked182 : fastCheckList band b182=true := by decide +kernel

def b183 : List (Rectangle × FastWitness) := [(r1464,⟨67,41,41⟩),(r1465,⟨67,41,41⟩),(r1466,⟨67,41,41⟩),(r1467,⟨67,41,41⟩),(r1468,⟨67,41,41⟩),(r1469,⟨67,41,41⟩),(r1470,⟨67,41,41⟩),(r1471,⟨67,41,41⟩)]
theorem checked183 : fastCheckList band b183=true := by decide +kernel

def b184 : List (Rectangle × FastWitness) := [(r1472,⟨67,41,41⟩),(r1473,⟨67,41,41⟩),(r1474,⟨67,41,41⟩),(r1475,⟨67,41,41⟩),(r1476,⟨67,41,41⟩),(r1477,⟨67,41,41⟩),(r1478,⟨67,41,41⟩),(r1479,⟨67,41,41⟩)]
theorem checked184 : fastCheckList band b184=true := by decide +kernel

def b185 : List (Rectangle × FastWitness) := [(r1480,⟨67,41,41⟩),(r1481,⟨67,41,41⟩),(r1482,⟨67,41,41⟩),(r1483,⟨67,41,41⟩),(r1484,⟨67,41,41⟩),(r1485,⟨67,41,41⟩),(r1486,⟨67,41,41⟩),(r1487,⟨67,41,41⟩)]
theorem checked185 : fastCheckList band b185=true := by decide +kernel

def b186 : List (Rectangle × FastWitness) := [(r1488,⟨67,41,41⟩),(r1489,⟨67,41,41⟩),(r1490,⟨67,41,41⟩),(r1491,⟨67,41,41⟩),(r1492,⟨67,41,41⟩),(r1493,⟨67,41,41⟩),(r1494,⟨67,41,41⟩),(r1495,⟨67,41,41⟩)]
theorem checked186 : fastCheckList band b186=true := by decide +kernel

def b187 : List (Rectangle × FastWitness) := [(r1496,⟨67,41,41⟩),(r1497,⟨67,41,41⟩),(r1498,⟨67,41,41⟩),(r1499,⟨67,41,41⟩),(r1500,⟨67,41,41⟩),(r1501,⟨67,41,41⟩),(r1502,⟨67,41,41⟩),(r1503,⟨67,41,41⟩)]
theorem checked187 : fastCheckList band b187=true := by decide +kernel

def b188 : List (Rectangle × FastWitness) := [(r1504,⟨67,41,41⟩),(r1505,⟨67,41,41⟩),(r1506,⟨67,41,41⟩),(r1507,⟨67,41,41⟩),(r1508,⟨67,41,41⟩),(r1509,⟨67,41,41⟩),(r1510,⟨67,41,41⟩),(r1511,⟨67,41,41⟩)]
theorem checked188 : fastCheckList band b188=true := by decide +kernel

def b189 : List (Rectangle × FastWitness) := [(r1512,⟨67,41,41⟩),(r1513,⟨67,41,41⟩),(r1514,⟨67,41,41⟩),(r1515,⟨67,41,41⟩),(r1516,⟨67,41,41⟩),(r1517,⟨67,41,41⟩),(r1518,⟨67,41,41⟩),(r1519,⟨67,41,41⟩)]
theorem checked189 : fastCheckList band b189=true := by decide +kernel

def b190 : List (Rectangle × FastWitness) := [(r1520,⟨67,41,41⟩),(r1521,⟨67,41,41⟩),(r1522,⟨67,41,41⟩),(r1523,⟨67,41,41⟩),(r1524,⟨67,41,41⟩),(r1525,⟨67,41,41⟩),(r1526,⟨67,41,41⟩),(r1527,⟨67,41,41⟩)]
theorem checked190 : fastCheckList band b190=true := by decide +kernel

def b191 : List (Rectangle × FastWitness) := [(r1528,⟨67,41,41⟩),(r1529,⟨67,41,41⟩),(r1530,⟨67,41,41⟩),(r1531,⟨67,41,41⟩),(r1532,⟨67,41,41⟩),(r1533,⟨67,41,41⟩),(r1534,⟨67,41,41⟩),(r1535,⟨67,41,41⟩)]
theorem checked191 : fastCheckList band b191=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


