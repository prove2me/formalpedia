-- Prove2me | Definitions.Def_Yukon_fbde9d252e66f1b67f8e0db3
-- name    : Yukon_fbde9d252e66f1b67f8e0db3
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:43:54.517247+00:00
-- url     : https://prove2.me/theorems/c061ae9d-43cd-42ea-9c3a-186fb9cfa45b
-- title:
--   Relative certificate source part 8/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_fbde9d252e66f1b67f8e0db3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjI5ZmM3N2M5N2Y1MTQ3YTJiMzMzZmQ5NjUxM2Y2OTk3ZjBjMDA0ZjEzNDhmZWEwNjNiMDhkNjU4MzZjMmQ2MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2ZiZGU5ZDI1MmU2NmYxYjY3ZjhlMGRiMyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2ZiZGU5ZDI1MmU2NmYxYjY3ZjhlMGRiMyIsInYiOjJ9]

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

def b192 : List (Rectangle × FastWitness) := [(r1536,⟨67,41,41⟩),(r1537,⟨67,41,41⟩),(r1538,⟨67,41,41⟩),(r1539,⟨67,41,41⟩),(r1540,⟨67,41,41⟩),(r1541,⟨67,41,41⟩),(r1542,⟨67,41,41⟩),(r1543,⟨67,41,41⟩)]
theorem checked192 : fastCheckList band b192=true := by decide +kernel

def b193 : List (Rectangle × FastWitness) := [(r1544,⟨67,41,41⟩),(r1545,⟨67,41,41⟩),(r1546,⟨67,41,41⟩),(r1547,⟨67,41,41⟩),(r1548,⟨67,41,41⟩),(r1549,⟨67,41,41⟩),(r1550,⟨67,41,41⟩),(r1551,⟨67,41,41⟩)]
theorem checked193 : fastCheckList band b193=true := by decide +kernel

def b194 : List (Rectangle × FastWitness) := [(r1552,⟨67,41,41⟩),(r1553,⟨67,41,41⟩),(r1554,⟨67,41,41⟩),(r1555,⟨67,41,41⟩),(r1556,⟨67,41,41⟩),(r1557,⟨67,41,41⟩),(r1558,⟨67,41,41⟩),(r1559,⟨67,41,41⟩)]
theorem checked194 : fastCheckList band b194=true := by decide +kernel

def b195 : List (Rectangle × FastWitness) := [(r1560,⟨67,41,41⟩),(r1561,⟨67,41,41⟩),(r1562,⟨67,41,41⟩),(r1563,⟨67,41,41⟩),(r1564,⟨67,41,41⟩),(r1565,⟨67,41,41⟩),(r1566,⟨67,41,41⟩),(r1567,⟨67,41,41⟩)]
theorem checked195 : fastCheckList band b195=true := by decide +kernel

def b196 : List (Rectangle × FastWitness) := [(r1568,⟨67,41,41⟩),(r1569,⟨67,41,41⟩),(r1570,⟨67,41,41⟩),(r1571,⟨67,41,41⟩),(r1572,⟨67,41,41⟩),(r1573,⟨67,41,41⟩),(r1574,⟨67,41,41⟩),(r1575,⟨67,41,41⟩)]
theorem checked196 : fastCheckList band b196=true := by decide +kernel

def b197 : List (Rectangle × FastWitness) := [(r1576,⟨67,41,41⟩),(r1577,⟨67,41,41⟩),(r1578,⟨67,41,41⟩),(r1579,⟨67,41,41⟩),(r1580,⟨67,41,41⟩),(r1581,⟨67,41,41⟩),(r1582,⟨67,41,41⟩),(r1583,⟨67,41,41⟩)]
theorem checked197 : fastCheckList band b197=true := by decide +kernel

def b198 : List (Rectangle × FastWitness) := [(r1584,⟨67,41,41⟩),(r1585,⟨67,41,41⟩),(r1586,⟨67,41,41⟩),(r1587,⟨67,41,41⟩),(r1588,⟨67,41,41⟩),(r1589,⟨67,41,41⟩),(r1590,⟨67,41,41⟩),(r1591,⟨67,41,41⟩)]
theorem checked198 : fastCheckList band b198=true := by decide +kernel

def b199 : List (Rectangle × FastWitness) := [(r1592,⟨67,41,41⟩),(r1593,⟨67,41,41⟩),(r1594,⟨67,41,41⟩),(r1595,⟨67,41,41⟩),(r1596,⟨67,41,41⟩),(r1597,⟨67,41,41⟩),(r1598,⟨67,41,41⟩),(r1599,⟨67,41,41⟩)]
theorem checked199 : fastCheckList band b199=true := by decide +kernel

def b200 : List (Rectangle × FastWitness) := [(r1600,⟨67,41,41⟩),(r1601,⟨67,41,41⟩),(r1602,⟨67,41,41⟩),(r1603,⟨67,41,41⟩),(r1604,⟨67,41,41⟩),(r1605,⟨67,41,41⟩),(r1606,⟨67,41,41⟩),(r1607,⟨67,41,41⟩)]
theorem checked200 : fastCheckList band b200=true := by decide +kernel

def b201 : List (Rectangle × FastWitness) := [(r1608,⟨67,41,41⟩),(r1609,⟨67,41,41⟩),(r1610,⟨67,41,41⟩),(r1611,⟨67,41,41⟩),(r1612,⟨67,41,41⟩),(r1613,⟨67,41,41⟩),(r1614,⟨67,41,41⟩),(r1615,⟨67,41,41⟩)]
theorem checked201 : fastCheckList band b201=true := by decide +kernel

def b202 : List (Rectangle × FastWitness) := [(r1616,⟨67,41,41⟩),(r1617,⟨67,41,41⟩),(r1618,⟨67,41,41⟩),(r1619,⟨67,41,41⟩),(r1620,⟨67,41,41⟩),(r1621,⟨67,41,41⟩),(r1622,⟨67,41,41⟩),(r1623,⟨67,41,41⟩)]
theorem checked202 : fastCheckList band b202=true := by decide +kernel

def b203 : List (Rectangle × FastWitness) := [(r1624,⟨67,41,41⟩),(r1625,⟨67,41,41⟩),(r1626,⟨67,41,41⟩),(r1627,⟨67,41,41⟩),(r1628,⟨67,41,41⟩),(r1629,⟨67,41,41⟩),(r1630,⟨67,41,41⟩),(r1631,⟨67,41,41⟩)]
theorem checked203 : fastCheckList band b203=true := by decide +kernel

def b204 : List (Rectangle × FastWitness) := [(r1632,⟨67,41,41⟩),(r1633,⟨67,41,41⟩),(r1634,⟨67,41,41⟩),(r1635,⟨67,41,41⟩),(r1636,⟨67,41,41⟩),(r1637,⟨67,41,41⟩),(r1638,⟨67,41,41⟩),(r1639,⟨67,41,41⟩)]
theorem checked204 : fastCheckList band b204=true := by decide +kernel

def b205 : List (Rectangle × FastWitness) := [(r1640,⟨67,41,41⟩),(r1641,⟨67,41,41⟩),(r1642,⟨67,41,41⟩),(r1643,⟨67,41,41⟩),(r1644,⟨67,41,41⟩),(r1645,⟨67,41,41⟩),(r1646,⟨67,41,41⟩),(r1647,⟨67,41,41⟩)]
theorem checked205 : fastCheckList band b205=true := by decide +kernel

def b206 : List (Rectangle × FastWitness) := [(r1648,⟨67,41,41⟩),(r1649,⟨67,41,41⟩),(r1650,⟨67,41,41⟩),(r1651,⟨67,41,41⟩),(r1652,⟨67,41,41⟩),(r1653,⟨67,41,41⟩),(r1654,⟨67,41,41⟩),(r1655,⟨67,41,41⟩)]
theorem checked206 : fastCheckList band b206=true := by decide +kernel

def b207 : List (Rectangle × FastWitness) := [(r1656,⟨67,41,41⟩),(r1657,⟨67,41,41⟩),(r1658,⟨67,41,41⟩),(r1659,⟨67,41,41⟩),(r1660,⟨67,41,41⟩),(r1661,⟨67,41,41⟩),(r1662,⟨67,41,41⟩),(r1663,⟨67,41,41⟩)]
theorem checked207 : fastCheckList band b207=true := by decide +kernel

def b208 : List (Rectangle × FastWitness) := [(r1664,⟨67,41,41⟩),(r1665,⟨67,41,41⟩),(r1666,⟨67,41,41⟩),(r1667,⟨67,41,41⟩),(r1668,⟨67,41,41⟩),(r1669,⟨67,41,41⟩),(r1670,⟨67,41,41⟩),(r1671,⟨67,41,41⟩)]
theorem checked208 : fastCheckList band b208=true := by decide +kernel

def b209 : List (Rectangle × FastWitness) := [(r1672,⟨67,41,41⟩),(r1673,⟨67,41,41⟩),(r1674,⟨67,41,41⟩),(r1675,⟨67,41,41⟩),(r1676,⟨67,41,41⟩),(r1677,⟨67,41,41⟩),(r1678,⟨67,41,41⟩),(r1679,⟨67,41,41⟩)]
theorem checked209 : fastCheckList band b209=true := by decide +kernel

def b210 : List (Rectangle × FastWitness) := [(r1680,⟨67,41,41⟩),(r1681,⟨67,41,41⟩),(r1682,⟨67,41,41⟩),(r1683,⟨67,41,41⟩),(r1684,⟨67,41,41⟩),(r1685,⟨67,41,41⟩),(r1686,⟨67,41,41⟩),(r1687,⟨67,41,41⟩)]
theorem checked210 : fastCheckList band b210=true := by decide +kernel

def b211 : List (Rectangle × FastWitness) := [(r1688,⟨67,41,41⟩),(r1689,⟨67,41,41⟩),(r1690,⟨67,41,41⟩),(r1691,⟨67,41,41⟩),(r1692,⟨67,41,41⟩),(r1693,⟨67,41,41⟩),(r1694,⟨67,41,41⟩),(r1695,⟨67,41,41⟩)]
theorem checked211 : fastCheckList band b211=true := by decide +kernel

def b212 : List (Rectangle × FastWitness) := [(r1696,⟨67,41,41⟩),(r1697,⟨67,41,41⟩),(r1698,⟨67,41,41⟩),(r1699,⟨67,41,41⟩),(r1700,⟨67,41,41⟩),(r1701,⟨67,41,41⟩),(r1702,⟨67,41,41⟩),(r1703,⟨67,41,41⟩)]
theorem checked212 : fastCheckList band b212=true := by decide +kernel

def b213 : List (Rectangle × FastWitness) := [(r1704,⟨67,41,41⟩),(r1705,⟨67,41,41⟩),(r1706,⟨67,41,41⟩),(r1707,⟨67,41,41⟩),(r1708,⟨67,41,41⟩),(r1709,⟨67,41,41⟩),(r1710,⟨67,41,41⟩),(r1711,⟨67,41,41⟩)]
theorem checked213 : fastCheckList band b213=true := by decide +kernel

def b214 : List (Rectangle × FastWitness) := [(r1712,⟨67,41,41⟩),(r1713,⟨67,41,41⟩),(r1714,⟨67,41,41⟩),(r1715,⟨67,41,41⟩),(r1716,⟨67,41,41⟩),(r1717,⟨67,41,41⟩),(r1718,⟨67,41,41⟩),(r1719,⟨67,41,41⟩)]
theorem checked214 : fastCheckList band b214=true := by decide +kernel

def b215 : List (Rectangle × FastWitness) := [(r1720,⟨67,41,41⟩),(r1721,⟨67,41,41⟩),(r1722,⟨67,41,41⟩),(r1723,⟨67,41,41⟩),(r1724,⟨67,41,41⟩),(r1725,⟨67,41,41⟩),(r1726,⟨67,41,41⟩),(r1727,⟨67,41,41⟩)]
theorem checked215 : fastCheckList band b215=true := by decide +kernel

def b216 : List (Rectangle × FastWitness) := [(r1728,⟨67,41,41⟩),(r1729,⟨67,41,41⟩),(r1730,⟨67,41,41⟩),(r1731,⟨67,41,41⟩),(r1732,⟨67,41,41⟩),(r1733,⟨67,41,41⟩),(r1734,⟨67,41,41⟩),(r1735,⟨67,41,41⟩)]
theorem checked216 : fastCheckList band b216=true := by decide +kernel

def b217 : List (Rectangle × FastWitness) := [(r1736,⟨67,41,41⟩),(r1737,⟨67,41,41⟩),(r1738,⟨67,41,41⟩),(r1739,⟨67,41,41⟩),(r1740,⟨67,41,41⟩),(r1741,⟨67,41,41⟩),(r1742,⟨67,41,41⟩),(r1743,⟨67,41,41⟩)]
theorem checked217 : fastCheckList band b217=true := by decide +kernel

def b218 : List (Rectangle × FastWitness) := [(r1744,⟨67,41,41⟩),(r1745,⟨67,41,41⟩),(r1746,⟨67,41,41⟩),(r1747,⟨67,41,41⟩),(r1748,⟨67,41,41⟩),(r1749,⟨67,41,41⟩),(r1750,⟨67,41,41⟩),(r1751,⟨67,41,41⟩)]
theorem checked218 : fastCheckList band b218=true := by decide +kernel

def b219 : List (Rectangle × FastWitness) := [(r1752,⟨67,41,41⟩),(r1753,⟨67,41,41⟩),(r1754,⟨67,41,41⟩),(r1755,⟨67,41,41⟩),(r1756,⟨67,41,41⟩),(r1757,⟨67,41,41⟩),(r1758,⟨67,41,41⟩),(r1759,⟨67,41,41⟩)]
theorem checked219 : fastCheckList band b219=true := by decide +kernel

def b220 : List (Rectangle × FastWitness) := [(r1760,⟨67,41,41⟩),(r1761,⟨67,41,41⟩),(r1762,⟨67,41,41⟩),(r1763,⟨67,41,41⟩),(r1764,⟨67,41,41⟩),(r1765,⟨67,41,41⟩),(r1766,⟨67,41,41⟩),(r1767,⟨67,41,41⟩)]
theorem checked220 : fastCheckList band b220=true := by decide +kernel

def b221 : List (Rectangle × FastWitness) := [(r1768,⟨67,41,41⟩),(r1769,⟨67,41,41⟩),(r1770,⟨67,41,41⟩),(r1771,⟨67,41,41⟩),(r1772,⟨67,41,41⟩),(r1773,⟨67,41,41⟩),(r1774,⟨67,41,41⟩),(r1775,⟨67,41,41⟩)]
theorem checked221 : fastCheckList band b221=true := by decide +kernel

def b222 : List (Rectangle × FastWitness) := [(r1776,⟨67,41,41⟩),(r1777,⟨67,41,41⟩),(r1778,⟨67,41,41⟩),(r1779,⟨67,41,41⟩),(r1780,⟨67,41,41⟩),(r1781,⟨67,41,41⟩),(r1782,⟨67,41,41⟩),(r1783,⟨67,41,41⟩)]
theorem checked222 : fastCheckList band b222=true := by decide +kernel

def b223 : List (Rectangle × FastWitness) := [(r1784,⟨67,41,41⟩),(r1785,⟨67,41,41⟩),(r1786,⟨67,41,41⟩),(r1787,⟨67,41,41⟩),(r1788,⟨67,41,41⟩),(r1789,⟨67,41,41⟩),(r1790,⟨67,41,41⟩),(r1791,⟨67,41,41⟩)]
theorem checked223 : fastCheckList band b223=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


