-- Prove2me | Definitions.Def_OAIQ106E022
-- name    : OAIQ106E022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-06T00:44:59.901196+00:00
-- url     : https://prove2.me/theorems/3e95ffa4-df45-406f-9872-2183914b9051
-- title:
--   Definitions bundle OAIQ106E022 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block1.rows7_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_1`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_2`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_3`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_4`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_5`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_6`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_7`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_8`, `OAI.MUB6.Certificate.GramEntries.Block1.rows9_9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block1Row7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row7.lean), [`MutuallyUnbiased_GramEntries_Block1Row9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block1Row9.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E015`, `OAIQ106E018` and `OAIQ106E021` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_7_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval9_8_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEval_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E015
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E021

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows7_6 : Fin GramFunctions.Block1.form7.size → Integer.Sparse Key := ![row1290, row1291, row1292, row1293, row1294, row1295, row1296, row1297, row1298, row1299, row1300, row1301, row1302, row1303, row1304, row1305, row1306, row1307, row1308, row1309, row1310, row1311, row1312, row1313, row1314, row1315, row1316, row1317, row1318, row1319]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_1 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1494, row1495, row1496, row1497, row1498, row1499, row1500, row1501, row1502, row1503, row1504, row1505, row1506, row1507, row1508, row1509, row1510, row1511, row1512, row1513, row1514, row1515, row1516, row1517, row1518, row1519, row1520, row1521, row1522, row1523]

def rows9_2 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1524, row1525, row1526, row1527, row1528, row1529, row1530, row1531, row1532, row1533, row1534, row1535, row1536, row1537, row1538, row1539, row1540, row1541, row1542, row1543, row1544, row1545, row1546, row1547, row1548, row1549, row1550, row1551, row1552, row1553]

def rows9_3 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1554, row1555, row1556, row1557, row1558, row1559, row1560, row1561, row1562, row1563, row1564, row1565, row1566, row1567, row1568, row1569, row1570, row1571, row1572, row1573, row1574, row1575, row1576, row1577, row1578, row1579, row1580, row1581, row1582, row1583]

def rows9_4 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1584, row1585, row1586, row1587, row1588, row1589, row1590, row1591, row1592, row1593, row1594, row1595, row1596, row1597, row1598, row1599, row1600, row1601, row1602, row1603, row1604, row1605, row1606, row1607, row1608, row1609, row1610, row1611, row1612, row1613]

def rows9_5 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1614, row1615, row1616, row1617, row1618, row1619, row1620, row1621, row1622, row1623, row1624, row1625, row1626, row1627, row1628, row1629, row1630, row1631, row1632, row1633, row1634, row1635, row1636, row1637, row1638, row1639, row1640, row1641, row1642, row1643]

def rows9_6 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1644, row1645, row1646, row1647, row1648, row1649, row1650, row1651, row1652, row1653, row1654, row1655, row1656, row1657, row1658, row1659, row1660, row1661, row1662, row1663, row1664, row1665, row1666, row1667, row1668, row1669, row1670, row1671, row1672, row1673]

def rows9_7 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1674, row1675, row1676, row1677, row1678, row1679, row1680, row1681, row1682, row1683, row1684, row1685, row1686, row1687, row1688, row1689, row1690, row1691, row1692, row1693, row1694, row1695, row1696, row1697, row1698, row1699, row1700, row1701, row1702, row1703]

def rows9_8 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1704, row1705, row1706, row1707, row1708, row1709, row1710, row1711, row1712, row1713, row1714, row1715, row1716, row1717, row1718, row1719, row1720, row1721, row1722, row1723, row1724, row1725, row1726, row1727, row1728, row1729, row1730, row1731, row1732, row1733]

def rows9_9 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1734, row1735, row1736, row1737, row1738, row1739, row1740, row1741, row1742, row1743, row1744, row1745, row1746, row1747, row1748, row1749, row1750, row1751, row1752, row1753, row1754, row1755, row1756, row1757, row1758, row1759, row1760, row1761, row1762, row1763]

end MUB6.Certificate.GramEntries.Block1

end OAI
end


