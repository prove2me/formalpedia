-- Prove2me | Definitions.Def_OAIQ106E075
-- name    : OAIQ106E075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T20:41:29.24069+00:00
-- url     : https://prove2.me/theorems/cad289f9-f4f6-4b37-80a5-da995db1b32b
-- title:
--   Definitions bundle OAIQ106E075 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedData.sourceChunk12`, `OAI.MUB6.Certificate.MixedData.sourceChunk13`, `OAI.MUB6.Certificate.MixedData.sourceChunk14`, `OAI.MUB6.Certificate.MixedData.sourceChunk15`, `OAI.MUB6.Certificate.MixedData.sourceChunk16`, `OAI.MUB6.Certificate.MixedData.sourceChunk17`, `OAI.MUB6.Certificate.MixedData.sourceChunk18`, `OAI.MUB6.Certificate.MixedData.sourceChunk2`, `OAI.MUB6.Certificate.MixedData.sourceChunk3`, `OAI.MUB6.Certificate.MixedData.sourceChunk4`, `OAI.MUB6.Certificate.MixedData.sourceChunk5`, `OAI.MUB6.Certificate.MixedData.sourceChunk6`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedData_Source12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source12.lean), [`MutuallyUnbiased_MixedData_Source13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source13.lean), [`MutuallyUnbiased_MixedData_Source14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source14.lean), [`MutuallyUnbiased_MixedData_Source15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source15.lean), [`MutuallyUnbiased_MixedData_Source16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source16.lean), [`MutuallyUnbiased_MixedData_Source17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source17.lean), [`MutuallyUnbiased_MixedData_Source18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source18.lean), [`MutuallyUnbiased_MixedData_Source2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source2.lean), [`MutuallyUnbiased_MixedData_Source3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source3.lean), [`MutuallyUnbiased_MixedData_Source4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source4.lean), [`MutuallyUnbiased_MixedData_Source5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source5.lean), [`MutuallyUnbiased_MixedData_Source6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source6.lean).
--
--   **Imports.** It imports the bundle `OAIQ106E070` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E077`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E070

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk12 : Array (Integer.Sparse (Fin 3237)) := #[row1536, row1537, row1538, row1539, row1540, row1541, row1542, row1543, row1544, row1545, row1546, row1547, row1548, row1549, row1550, row1551, row1552, row1553, row1554, row1555, row1556, row1557, row1558, row1559, row1560, row1561, row1562, row1563, row1564, row1565, row1566, row1567, row1568, row1569, row1570, row1571, row1572, row1573, row1574, row1575, row1576, row1577, row1578, row1579, row1580, row1581, row1582, row1583, row1584, row1585, row1586, row1587, row1588, row1589, row1590, row1591, row1592, row1593, row1594, row1595, row1596, row1597, row1598, row1599, row1600, row1601, row1602, row1603, row1604, row1605, row1606, row1607, row1608, row1609, row1610, row1611, row1612, row1613, row1614, row1615, row1616, row1617, row1618, row1619, row1620, row1621, row1622, row1623, row1624, row1625, row1626, row1627, row1628, row1629, row1630, row1631, row1632, row1633, row1634, row1635, row1636, row1637, row1638, row1639, row1640, row1641, row1642, row1643, row1644, row1645, row1646, row1647, row1648, row1649, row1650, row1651, row1652, row1653, row1654, row1655, row1656, row1657, row1658, row1659, row1660, row1661, row1662, row1663]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk13 : Array (Integer.Sparse (Fin 3237)) := #[row1664, row1665, row1666, row1667, row1668, row1669, row1670, row1671, row1672, row1673, row1674, row1675, row1676, row1677, row1678, row1679, row1680, row1681, row1682, row1683, row1684, row1685, row1686, row1687, row1688, row1689, row1690, row1691, row1692, row1693, row1694, row1695, row1696, row1697, row1698, row1699, row1700, row1701, row1702, row1703, row1704, row1705, row1706, row1707, row1708, row1709, row1710, row1711, row1712, row1713, row1714, row1715, row1716, row1717, row1718, row1719, row1720, row1721, row1722, row1723, row1724, row1725, row1726, row1727, row1728, row1729, row1730, row1731, row1732, row1733, row1734, row1735, row1736, row1737, row1738, row1739, row1740, row1741, row1742, row1743, row1744, row1745, row1746, row1747, row1748, row1749, row1750, row1751, row1752, row1753, row1754, row1755, row1756, row1757, row1758, row1759, row1760, row1761, row1762, row1763, row1764, row1765, row1766, row1767, row1768, row1769, row1770, row1771, row1772, row1773, row1774, row1775, row1776, row1777, row1778, row1779, row1780, row1781, row1782, row1783, row1784, row1785, row1786, row1787, row1788, row1789, row1790, row1791]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk14 : Array (Integer.Sparse (Fin 3237)) := #[row1792, row1793, row1794, row1795, row1796, row1797, row1798, row1799, row1800, row1801, row1802, row1803, row1804, row1805, row1806, row1807, row1808, row1809, row1810, row1811, row1812, row1813, row1814, row1815, row1816, row1817, row1818, row1819, row1820, row1821, row1822, row1823, row1824, row1825, row1826, row1827, row1828, row1829, row1830, row1831, row1832, row1833, row1834, row1835, row1836, row1837, row1838, row1839, row1840, row1841, row1842, row1843, row1844, row1845, row1846, row1847, row1848, row1849, row1850, row1851, row1852, row1853, row1854, row1855, row1856, row1857, row1858, row1859, row1860, row1861, row1862, row1863, row1864, row1865, row1866, row1867, row1868, row1869, row1870, row1871, row1872, row1873, row1874, row1875, row1876, row1877, row1878, row1879, row1880, row1881, row1882, row1883, row1884, row1885, row1886, row1887, row1888, row1889, row1890, row1891, row1892, row1893, row1894, row1895, row1896, row1897, row1898, row1899, row1900, row1901, row1902, row1903, row1904, row1905, row1906, row1907, row1908, row1909, row1910, row1911, row1912, row1913, row1914, row1915, row1916, row1917, row1918, row1919]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk15 : Array (Integer.Sparse (Fin 3237)) := #[row1920, row1921, row1922, row1923, row1924, row1925, row1926, row1927, row1928, row1929, row1930, row1931, row1932, row1933, row1934, row1935, row1936, row1937, row1938, row1939, row1940, row1941, row1942, row1943, row1944, row1945, row1946, row1947, row1948, row1949, row1950, row1951, row1952, row1953, row1954, row1955, row1956, row1957, row1958, row1959, row1960, row1961, row1962, row1963, row1964, row1965, row1966, row1967, row1968, row1969, row1970, row1971, row1972, row1973, row1974, row1975, row1976, row1977, row1978, row1979, row1980, row1981, row1982, row1983, row1984, row1985, row1986, row1987, row1988, row1989, row1990, row1991, row1992, row1993, row1994, row1995, row1996, row1997, row1998, row1999, row2000, row2001, row2002, row2003, row2004, row2005, row2006, row2007, row2008, row2009, row2010, row2011, row2012, row2013, row2014, row2015, row2016, row2017, row2018, row2019, row2020, row2021, row2022, row2023, row2024, row2025, row2026, row2027, row2028, row2029, row2030, row2031, row2032, row2033, row2034, row2035, row2036, row2037, row2038, row2039, row2040, row2041, row2042, row2043, row2044, row2045, row2046, row2047]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk16 : Array (Integer.Sparse (Fin 3237)) := #[row2048, row2049, row2050, row2051, row2052, row2053, row2054, row2055, row2056, row2057, row2058, row2059, row2060, row2061, row2062, row2063, row2064, row2065, row2066, row2067, row2068, row2069, row2070, row2071, row2072, row2073, row2074, row2075, row2076, row2077, row2078, row2079, row2080, row2081, row2082, row2083, row2084, row2085, row2086, row2087, row2088, row2089, row2090, row2091, row2092, row2093, row2094, row2095, row2096, row2097, row2098, row2099, row2100, row2101, row2102, row2103, row2104, row2105, row2106, row2107, row2108, row2109, row2110, row2111, row2112, row2113, row2114, row2115, row2116, row2117, row2118, row2119, row2120, row2121, row2122, row2123, row2124, row2125, row2126, row2127, row2128, row2129, row2130, row2131, row2132, row2133, row2134, row2135, row2136, row2137, row2138, row2139, row2140, row2141, row2142, row2143, row2144, row2145, row2146, row2147, row2148, row2149, row2150, row2151, row2152, row2153, row2154, row2155, row2156, row2157, row2158, row2159, row2160, row2161, row2162, row2163, row2164, row2165, row2166, row2167, row2168, row2169, row2170, row2171, row2172, row2173, row2174, row2175]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk17 : Array (Integer.Sparse (Fin 3237)) := #[row2176, row2177, row2178, row2179, row2180, row2181, row2182, row2183, row2184, row2185, row2186, row2187, row2188, row2189, row2190, row2191, row2192, row2193, row2194, row2195, row2196, row2197, row2198, row2199, row2200, row2201, row2202, row2203, row2204, row2205, row2206, row2207, row2208, row2209, row2210, row2211, row2212, row2213, row2214, row2215, row2216, row2217, row2218, row2219, row2220, row2221, row2222, row2223, row2224, row2225, row2226, row2227, row2228, row2229, row2230, row2231, row2232, row2233, row2234, row2235, row2236, row2237, row2238, row2239, row2240, row2241, row2242, row2243, row2244, row2245, row2246, row2247, row2248, row2249, row2250, row2251, row2252, row2253, row2254, row2255, row2256, row2257, row2258, row2259, row2260, row2261, row2262, row2263, row2264, row2265, row2266, row2267, row2268, row2269, row2270, row2271, row2272, row2273, row2274, row2275, row2276, row2277, row2278, row2279, row2280, row2281, row2282, row2283, row2284, row2285, row2286, row2287, row2288, row2289, row2290, row2291, row2292, row2293, row2294, row2295, row2296, row2297, row2298, row2299, row2300, row2301, row2302, row2303]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk18 : Array (Integer.Sparse (Fin 3237)) := #[row2304, row2305, row2306, row2307, row2308, row2309, row2310, row2311, row2312, row2313, row2314, row2315, row2316, row2317, row2318, row2319, row2320, row2321, row2322, row2323, row2324, row2325, row2326, row2327, row2328, row2329, row2330, row2331, row2332, row2333, row2334, row2335, row2336, row2337, row2338, row2339, row2340, row2341, row2342, row2343, row2344, row2345, row2346, row2347, row2348, row2349, row2350, row2351, row2352, row2353, row2354, row2355, row2356, row2357, row2358, row2359, row2360, row2361, row2362, row2363, row2364, row2365, row2366, row2367, row2368, row2369, row2370, row2371, row2372, row2373, row2374, row2375, row2376, row2377, row2378, row2379, row2380, row2381, row2382, row2383, row2384, row2385, row2386, row2387, row2388, row2389, row2390, row2391, row2392, row2393, row2394, row2395, row2396, row2397, row2398, row2399, row2400, row2401, row2402, row2403, row2404, row2405, row2406, row2407, row2408, row2409, row2410, row2411, row2412, row2413, row2414, row2415, row2416, row2417, row2418, row2419, row2420, row2421, row2422, row2423, row2424]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk2 : Array (Integer.Sparse (Fin 3237)) := #[row256, row257, row258, row259, row260, row261, row262, row263, row264, row265, row266, row267, row268, row269, row270, row271, row272, row273, row274, row275, row276, row277, row278, row279, row280, row281, row282, row283, row284, row285, row286, row287, row288, row289, row290, row291, row292, row293, row294, row295, row296, row297, row298, row299, row300, row301, row302, row303, row304, row305, row306, row307, row308, row309, row310, row311, row312, row313, row314, row315, row316, row317, row318, row319, row320, row321, row322, row323, row324, row325, row326, row327, row328, row329, row330, row331, row332, row333, row334, row335, row336, row337, row338, row339, row340, row341, row342, row343, row344, row345, row346, row347, row348, row349, row350, row351, row352, row353, row354, row355, row356, row357, row358, row359, row360, row361, row362, row363, row364, row365, row366, row367, row368, row369, row370, row371, row372, row373, row374, row375, row376, row377, row378, row379, row380, row381, row382, row383]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk3 : Array (Integer.Sparse (Fin 3237)) := #[row384, row385, row386, row387, row388, row389, row390, row391, row392, row393, row394, row395, row396, row397, row398, row399, row400, row401, row402, row403, row404, row405, row406, row407, row408, row409, row410, row411, row412, row413, row414, row415, row416, row417, row418, row419, row420, row421, row422, row423, row424, row425, row426, row427, row428, row429, row430, row431, row432, row433, row434, row435, row436, row437, row438, row439, row440, row441, row442, row443, row444, row445, row446, row447, row448, row449, row450, row451, row452, row453, row454, row455, row456, row457, row458, row459, row460, row461, row462, row463, row464, row465, row466, row467, row468, row469, row470, row471, row472, row473, row474, row475, row476, row477, row478, row479, row480, row481, row482, row483, row484, row485, row486, row487, row488, row489, row490, row491, row492, row493, row494, row495, row496, row497, row498, row499, row500, row501, row502, row503, row504, row505, row506, row507, row508, row509, row510, row511]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk4 : Array (Integer.Sparse (Fin 3237)) := #[row512, row513, row514, row515, row516, row517, row518, row519, row520, row521, row522, row523, row524, row525, row526, row527, row528, row529, row530, row531, row532, row533, row534, row535, row536, row537, row538, row539, row540, row541, row542, row543, row544, row545, row546, row547, row548, row549, row550, row551, row552, row553, row554, row555, row556, row557, row558, row559, row560, row561, row562, row563, row564, row565, row566, row567, row568, row569, row570, row571, row572, row573, row574, row575, row576, row577, row578, row579, row580, row581, row582, row583, row584, row585, row586, row587, row588, row589, row590, row591, row592, row593, row594, row595, row596, row597, row598, row599, row600, row601, row602, row603, row604, row605, row606, row607, row608, row609, row610, row611, row612, row613, row614, row615, row616, row617, row618, row619, row620, row621, row622, row623, row624, row625, row626, row627, row628, row629, row630, row631, row632, row633, row634, row635, row636, row637, row638, row639]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk5 : Array (Integer.Sparse (Fin 3237)) := #[row640, row641, row642, row643, row644, row645, row646, row647, row648, row649, row650, row651, row652, row653, row654, row655, row656, row657, row658, row659, row660, row661, row662, row663, row664, row665, row666, row667, row668, row669, row670, row671, row672, row673, row674, row675, row676, row677, row678, row679, row680, row681, row682, row683, row684, row685, row686, row687, row688, row689, row690, row691, row692, row693, row694, row695, row696, row697, row698, row699, row700, row701, row702, row703, row704, row705, row706, row707, row708, row709, row710, row711, row712, row713, row714, row715, row716, row717, row718, row719, row720, row721, row722, row723, row724, row725, row726, row727, row728, row729, row730, row731, row732, row733, row734, row735, row736, row737, row738, row739, row740, row741, row742, row743, row744, row745, row746, row747, row748, row749, row750, row751, row752, row753, row754, row755, row756, row757, row758, row759, row760, row761, row762, row763, row764, row765, row766, row767]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def sourceChunk6 : Array (Integer.Sparse (Fin 3237)) := #[row768, row769, row770, row771, row772, row773, row774, row775, row776, row777, row778, row779, row780, row781, row782, row783, row784, row785, row786, row787, row788, row789, row790, row791, row792, row793, row794, row795, row796, row797, row798, row799, row800, row801, row802, row803, row804, row805, row806, row807, row808, row809, row810, row811, row812, row813, row814, row815, row816, row817, row818, row819, row820, row821, row822, row823, row824, row825, row826, row827, row828, row829, row830, row831, row832, row833, row834, row835, row836, row837, row838, row839, row840, row841, row842, row843, row844, row845, row846, row847, row848, row849, row850, row851, row852, row853, row854, row855, row856, row857, row858, row859, row860, row861, row862, row863, row864, row865, row866, row867, row868, row869, row870, row871, row872, row873, row874, row875, row876, row877, row878, row879, row880, row881, row882, row883, row884, row885, row886, row887, row888, row889, row890, row891, row892, row893, row894, row895]

end MUB6.Certificate.MixedData

end OAI
end


