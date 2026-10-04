-- Prove2me | Definitions.Def_Yukon_02045028de24018980e7b33a
-- name    : Yukon_02045028de24018980e7b33a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:05:40.506203+00:00
-- url     : https://prove2.me/theorems/d7f4ab64-adc2-4a91-9f15-a69ed80aac82
-- title:
--   Relative certificate source part 7/8
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B58T3294To3657Fast.lean
--
--   yukon-proof-operation:certificate-b58-module-Yukon_02045028de24018980e7b33a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWU2MGNlMDE1ZjZjYmNiZDhhMWUyMTQ1NmNkNDc5MjdmZjZjMDUwNjIzOGNjYzMyZGRjZWU0NzUxMDExZmMxZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1OC1tb2R1bGUtWXVrb25fMDIwNDUwMjhkZTI0MDE4OTgwZTdiMzNhIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMDIwNDUwMjhkZTI0MDE4OTgwZTdiMzNhIiwidiI6Mn0]

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

def b180 : List (Rectangle × FastWitness) := [(r1440,⟨70,47,48⟩),(r1441,⟨70,47,48⟩),(r1442,⟨70,47,48⟩),(r1443,⟨70,47,48⟩),(r1444,⟨70,47,48⟩),(r1445,⟨70,47,48⟩),(r1446,⟨70,47,48⟩),(r1447,⟨70,47,48⟩)]
theorem checked180 : fastCheckList band b180=true := by decide +kernel

def b181 : List (Rectangle × FastWitness) := [(r1448,⟨70,47,48⟩),(r1449,⟨70,47,48⟩),(r1450,⟨70,47,48⟩),(r1451,⟨70,47,48⟩),(r1452,⟨70,47,48⟩),(r1453,⟨70,47,48⟩),(r1454,⟨70,47,48⟩),(r1455,⟨70,47,48⟩)]
theorem checked181 : fastCheckList band b181=true := by decide +kernel

def b182 : List (Rectangle × FastWitness) := [(r1456,⟨70,47,48⟩),(r1457,⟨70,47,48⟩),(r1458,⟨70,47,48⟩),(r1459,⟨70,47,48⟩),(r1460,⟨70,47,48⟩),(r1461,⟨70,47,48⟩),(r1462,⟨70,47,48⟩),(r1463,⟨70,47,48⟩)]
theorem checked182 : fastCheckList band b182=true := by decide +kernel

def b183 : List (Rectangle × FastWitness) := [(r1464,⟨70,47,48⟩),(r1465,⟨70,47,48⟩),(r1466,⟨70,47,48⟩),(r1467,⟨70,47,48⟩),(r1468,⟨70,47,48⟩),(r1469,⟨70,48,48⟩),(r1470,⟨70,48,48⟩),(r1471,⟨70,48,48⟩)]
theorem checked183 : fastCheckList band b183=true := by decide +kernel

def b184 : List (Rectangle × FastWitness) := [(r1472,⟨70,48,48⟩),(r1473,⟨70,48,48⟩),(r1474,⟨70,48,48⟩),(r1475,⟨70,48,48⟩),(r1476,⟨70,48,48⟩),(r1477,⟨70,48,48⟩),(r1478,⟨70,48,48⟩),(r1479,⟨70,48,48⟩)]
theorem checked184 : fastCheckList band b184=true := by decide +kernel

def b185 : List (Rectangle × FastWitness) := [(r1480,⟨70,48,48⟩),(r1481,⟨70,48,48⟩),(r1482,⟨70,48,48⟩),(r1483,⟨70,48,48⟩),(r1484,⟨70,48,48⟩),(r1485,⟨70,48,48⟩),(r1486,⟨70,48,48⟩),(r1487,⟨70,48,48⟩)]
theorem checked185 : fastCheckList band b185=true := by decide +kernel

def b186 : List (Rectangle × FastWitness) := [(r1488,⟨70,48,48⟩),(r1489,⟨70,48,48⟩),(r1490,⟨70,48,48⟩),(r1491,⟨70,48,48⟩),(r1492,⟨70,48,48⟩),(r1493,⟨70,48,48⟩),(r1494,⟨70,48,48⟩),(r1495,⟨70,48,48⟩)]
theorem checked186 : fastCheckList band b186=true := by decide +kernel

def b187 : List (Rectangle × FastWitness) := [(r1496,⟨70,48,48⟩),(r1497,⟨70,48,48⟩),(r1498,⟨70,48,48⟩),(r1499,⟨70,48,48⟩),(r1500,⟨70,48,48⟩),(r1501,⟨70,48,48⟩),(r1502,⟨70,48,48⟩),(r1503,⟨70,48,48⟩)]
theorem checked187 : fastCheckList band b187=true := by decide +kernel

def b188 : List (Rectangle × FastWitness) := [(r1504,⟨70,48,48⟩),(r1505,⟨70,48,48⟩),(r1506,⟨70,48,49⟩),(r1507,⟨70,48,49⟩),(r1508,⟨70,48,49⟩),(r1509,⟨70,48,49⟩),(r1510,⟨70,48,49⟩),(r1511,⟨70,48,49⟩)]
theorem checked188 : fastCheckList band b188=true := by decide +kernel

def b189 : List (Rectangle × FastWitness) := [(r1512,⟨70,48,49⟩),(r1513,⟨70,48,49⟩),(r1514,⟨70,48,49⟩),(r1515,⟨70,48,49⟩),(r1516,⟨70,48,49⟩),(r1517,⟨70,49,50⟩),(r1518,⟨70,50,50⟩),(r1519,⟨70,50,50⟩)]
theorem checked189 : fastCheckList band b189=true := by decide +kernel

def b190 : List (Rectangle × FastWitness) := [(r1520,⟨70,50,50⟩),(r1521,⟨70,50,50⟩),(r1522,⟨70,50,50⟩),(r1523,⟨70,50,50⟩),(r1524,⟨70,50,50⟩),(r1525,⟨70,50,50⟩),(r1526,⟨70,50,50⟩),(r1527,⟨70,50,50⟩)]
theorem checked190 : fastCheckList band b190=true := by decide +kernel

def b191 : List (Rectangle × FastWitness) := [(r1528,⟨70,50,50⟩),(r1529,⟨70,50,50⟩),(r1530,⟨70,50,50⟩),(r1531,⟨70,50,50⟩),(r1532,⟨70,50,50⟩),(r1533,⟨70,50,50⟩),(r1534,⟨70,50,50⟩),(r1535,⟨70,50,50⟩)]
theorem checked191 : fastCheckList band b191=true := by decide +kernel

def b192 : List (Rectangle × FastWitness) := [(r1536,⟨70,50,50⟩),(r1537,⟨70,50,50⟩),(r1538,⟨70,50,50⟩),(r1539,⟨70,50,50⟩),(r1540,⟨70,50,50⟩),(r1541,⟨70,50,50⟩),(r1542,⟨70,50,50⟩),(r1543,⟨70,50,51⟩)]
theorem checked192 : fastCheckList band b192=true := by decide +kernel

def b193 : List (Rectangle × FastWitness) := [(r1544,⟨70,50,51⟩),(r1545,⟨70,50,51⟩),(r1546,⟨70,50,51⟩),(r1547,⟨70,50,51⟩),(r1548,⟨70,50,51⟩),(r1549,⟨70,50,51⟩),(r1550,⟨70,50,51⟩),(r1551,⟨70,50,51⟩)]
theorem checked193 : fastCheckList band b193=true := by decide +kernel

def b194 : List (Rectangle × FastWitness) := [(r1552,⟨70,50,51⟩),(r1553,⟨70,50,51⟩),(r1554,⟨70,50,51⟩),(r1555,⟨70,51,51⟩),(r1556,⟨70,51,51⟩),(r1557,⟨70,51,51⟩),(r1558,⟨70,51,51⟩),(r1559,⟨70,51,51⟩)]
theorem checked194 : fastCheckList band b194=true := by decide +kernel

def b195 : List (Rectangle × FastWitness) := [(r1560,⟨70,51,51⟩),(r1561,⟨70,51,51⟩),(r1562,⟨70,51,51⟩),(r1563,⟨70,51,51⟩),(r1564,⟨70,51,51⟩),(r1565,⟨70,51,51⟩),(r1566,⟨70,51,51⟩),(r1567,⟨70,51,51⟩)]
theorem checked195 : fastCheckList band b195=true := by decide +kernel

def b196 : List (Rectangle × FastWitness) := [(r1568,⟨70,51,51⟩),(r1569,⟨70,51,51⟩),(r1570,⟨70,51,51⟩),(r1571,⟨70,51,51⟩),(r1572,⟨70,51,51⟩),(r1573,⟨70,51,51⟩),(r1574,⟨70,51,51⟩),(r1575,⟨70,51,51⟩)]
theorem checked196 : fastCheckList band b196=true := by decide +kernel

def b197 : List (Rectangle × FastWitness) := [(r1576,⟨70,51,51⟩),(r1577,⟨70,51,51⟩),(r1578,⟨70,51,52⟩),(r1579,⟨70,51,52⟩),(r1580,⟨70,51,52⟩),(r1581,⟨70,51,52⟩),(r1582,⟨70,51,52⟩),(r1583,⟨70,51,52⟩)]
theorem checked197 : fastCheckList band b197=true := by decide +kernel

def b198 : List (Rectangle × FastWitness) := [(r1584,⟨70,51,52⟩),(r1585,⟨70,52,52⟩),(r1586,⟨70,52,52⟩),(r1587,⟨70,53,54⟩),(r1588,⟨70,53,54⟩),(r1589,⟨70,53,54⟩),(r1590,⟨70,54,54⟩),(r1591,⟨70,54,54⟩)]
theorem checked198 : fastCheckList band b198=true := by decide +kernel

def b199 : List (Rectangle × FastWitness) := [(r1592,⟨70,54,54⟩),(r1593,⟨70,54,54⟩),(r1594,⟨70,54,54⟩),(r1595,⟨70,54,54⟩),(r1596,⟨70,54,54⟩),(r1597,⟨70,54,54⟩),(r1598,⟨70,54,54⟩),(r1599,⟨70,54,54⟩)]
theorem checked199 : fastCheckList band b199=true := by decide +kernel

def b200 : List (Rectangle × FastWitness) := [(r1600,⟨70,54,54⟩),(r1601,⟨70,54,54⟩),(r1602,⟨70,54,54⟩),(r1603,⟨70,54,54⟩),(r1604,⟨70,54,54⟩),(r1605,⟨70,54,54⟩),(r1606,⟨70,54,54⟩),(r1607,⟨70,54,54⟩)]
theorem checked200 : fastCheckList band b200=true := by decide +kernel

def b201 : List (Rectangle × FastWitness) := [(r1608,⟨70,54,55⟩),(r1609,⟨70,54,55⟩),(r1610,⟨70,54,55⟩),(r1611,⟨70,55,55⟩),(r1612,⟨70,55,55⟩),(r1613,⟨70,55,55⟩),(r1614,⟨70,55,55⟩),(r1615,⟨70,55,55⟩)]
theorem checked201 : fastCheckList band b201=true := by decide +kernel

def b202 : List (Rectangle × FastWitness) := [(r1616,⟨70,55,55⟩),(r1617,⟨70,55,55⟩),(r1618,⟨70,55,55⟩),(r1619,⟨70,55,55⟩),(r1620,⟨70,55,55⟩),(r1621,⟨70,55,55⟩),(r1622,⟨70,55,55⟩),(r1623,⟨70,55,55⟩)]
theorem checked202 : fastCheckList band b202=true := by decide +kernel

def b203 : List (Rectangle × FastWitness) := [(r1624,⟨70,55,55⟩),(r1625,⟨70,55,56⟩),(r1626,⟨70,55,56⟩),(r1627,⟨70,56,56⟩),(r1628,⟨70,56,56⟩),(r1629,⟨70,56,56⟩),(r1630,⟨70,56,56⟩),(r1631,⟨70,56,56⟩)]
theorem checked203 : fastCheckList band b203=true := by decide +kernel

def b204 : List (Rectangle × FastWitness) := [(r1632,⟨70,56,56⟩),(r1633,⟨70,56,56⟩),(r1634,⟨70,56,56⟩),(r1635,⟨70,59,59⟩),(r1636,⟨70,59,59⟩),(r1637,⟨70,59,59⟩),(r1638,⟨70,59,59⟩),(r1639,⟨70,59,59⟩)]
theorem checked204 : fastCheckList band b204=true := by decide +kernel

def b205 : List (Rectangle × FastWitness) := [(r1640,⟨70,59,59⟩),(r1641,⟨70,59,59⟩),(r1642,⟨70,59,59⟩),(r1643,⟨70,59,59⟩),(r1644,⟨70,59,59⟩),(r1645,⟨70,59,60⟩),(r1646,⟨70,60,60⟩),(r1647,⟨70,60,60⟩)]
theorem checked205 : fastCheckList band b205=true := by decide +kernel

def b206 : List (Rectangle × FastWitness) := [(r1648,⟨70,60,60⟩),(r1649,⟨70,60,60⟩),(r1650,⟨70,60,60⟩),(r1651,⟨70,60,60⟩),(r1652,⟨70,60,60⟩),(r1653,⟨70,60,60⟩),(r1654,⟨70,60,60⟩),(r1655,⟨70,61,61⟩)]
theorem checked206 : fastCheckList band b206=true := by decide +kernel

def b207 : List (Rectangle × FastWitness) := [(r1656,⟨70,61,61⟩),(r1657,⟨70,61,61⟩),(r1658,⟨70,61,61⟩),(r1659,⟨70,61,61⟩),(r1660,⟨70,61,61⟩),(r1661,⟨70,61,61⟩),(r1662,⟨70,61,61⟩),(r1663,⟨70,62,62⟩)]
theorem checked207 : fastCheckList band b207=true := by decide +kernel

def b208 : List (Rectangle × FastWitness) := [(r1664,⟨70,62,62⟩),(r1665,⟨70,62,62⟩),(r1666,⟨70,62,62⟩),(r1667,⟨70,62,62⟩),(r1668,⟨70,62,62⟩),(r1669,⟨70,62,62⟩),(r1670,⟨70,63,63⟩),(r1671,⟨70,63,63⟩)]
theorem checked208 : fastCheckList band b208=true := by decide +kernel

def b209 : List (Rectangle × FastWitness) := [(r1672,⟨70,63,63⟩),(r1673,⟨70,63,63⟩),(r1674,⟨70,63,63⟩),(r1675,⟨70,63,63⟩),(r1676,⟨70,63,63⟩),(r1677,⟨70,64,64⟩),(r1678,⟨70,64,64⟩),(r1679,⟨70,64,64⟩)]
theorem checked209 : fastCheckList band b209=true := by decide +kernel

def b210 : List (Rectangle × FastWitness) := [(r1680,⟨70,64,64⟩),(r1681,⟨70,64,64⟩),(r1682,⟨70,64,64⟩)]
theorem checked210 : fastCheckList band b210=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR12B58T3294To3657Fast


