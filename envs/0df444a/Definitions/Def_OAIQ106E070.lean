-- Prove2me | Definitions.Def_OAIQ106E070
-- name    : OAIQ106E070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:21:09.349449+00:00
-- url     : https://prove2.me/theorems/c95e018f-4032-41b1-b673-d1e5b2cb3341
-- title:
--   Definitions bundle OAIQ106E070 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1777 declarations of OpenAI's Lean: 1777 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedData.row1504`, `OAI.MUB6.Certificate.MixedData.row1505`, `OAI.MUB6.Certificate.MixedData.row1506`, `OAI.MUB6.Certificate.MixedData.row1507`, `OAI.MUB6.Certificate.MixedData.row1508`, `OAI.MUB6.Certificate.MixedData.row1509`, `OAI.MUB6.Certificate.MixedData.row151`, `OAI.MUB6.Certificate.MixedData.row1510`, `OAI.MUB6.Certificate.MixedData.row1511`, `OAI.MUB6.Certificate.MixedData.row1512`, `OAI.MUB6.Certificate.MixedData.row1513`, `OAI.MUB6.Certificate.MixedData.row1514`, `OAI.MUB6.Certificate.MixedData.row1515`, `OAI.MUB6.Certificate.MixedData.row1516`, `OAI.MUB6.Certificate.MixedData.row1517`, `OAI.MUB6.Certificate.MixedData.row1518`, `OAI.MUB6.Certificate.MixedData.row1519`, `OAI.MUB6.Certificate.MixedData.row152`, `OAI.MUB6.Certificate.MixedData.row1520`, `OAI.MUB6.Certificate.MixedData.row1521`, `OAI.MUB6.Certificate.MixedData.row1522`, `OAI.MUB6.Certificate.MixedData.row1523`, `OAI.MUB6.Certificate.MixedData.row1524`, `OAI.MUB6.Certificate.MixedData.row1525`, `OAI.MUB6.Certificate.MixedData.row1526`, `OAI.MUB6.Certificate.MixedData.row1527`, `OAI.MUB6.Certificate.MixedData.row1528`, `OAI.MUB6.Certificate.MixedData.row1529`, `OAI.MUB6.Certificate.MixedData.row153`, `OAI.MUB6.Certificate.MixedData.row1530`, `OAI.MUB6.Certificate.MixedData.row1531`, `OAI.MUB6.Certificate.MixedData.row1532`, `OAI.MUB6.Certificate.MixedData.row1533`, `OAI.MUB6.Certificate.MixedData.row1534`, `OAI.MUB6.Certificate.MixedData.row1535`, `OAI.MUB6.Certificate.MixedData.row1536`, `OAI.MUB6.Certificate.MixedData.row1537`, `OAI.MUB6.Certificate.MixedData.row1538`, `OAI.MUB6.Certificate.MixedData.row1539`, `OAI.MUB6.Certificate.MixedData.row154` and 1737 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedData_Source0`, `MutuallyUnbiased_MixedData_Source1`, `MutuallyUnbiased_MixedData_Source11`, `MutuallyUnbiased_MixedData_Source12`, `MutuallyUnbiased_MixedData_Source13`, `MutuallyUnbiased_MixedData_Source14`, `MutuallyUnbiased_MixedData_Source15`, `MutuallyUnbiased_MixedData_Source16`, `MutuallyUnbiased_MixedData_Source17`, `MutuallyUnbiased_MixedData_Source18`, `MutuallyUnbiased_MixedData_Source2`, `MutuallyUnbiased_MixedData_Source3`, `MutuallyUnbiased_MixedData_Source4`, `MutuallyUnbiased_MixedData_Source5`, `MutuallyUnbiased_MixedData_Source6`, `MutuallyUnbiased_MixedData_Source7`.
--
--   **Imports.** It imports the bundle `OAIQ106E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E072`, `OAIQ106E073`, `OAIQ106E075` and `OAIQ106E076`; the statements `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound695_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E000

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row2 : Integer.Sparse (Fin 3237) := [(0, -35), (225, -40), (261, 75), (1593, 720), (1595, 360), (1611, 720), (2177, 720), (2694, 720), (2699, 1440), (2768, 720), (2769, 720)]

def row3 : Integer.Sparse (Fin 3237) := [(0, 26), (225, 40), (261, 150), (2159, -720), (2160, -720), (2567, -720), (2571, -360), (2574, -720), (2704, -1440), (2760, -720), (2763, -720)]

def row4 : Integer.Sparse (Fin 3237) := [(0, 1), (261, -1), (1934, -16), (1936, -4), (1950, -8), (2501, -16), (2502, -4), (2503, -8), (2575, -8), (2783, -16), (2786, -16), (2787, -8), (2803, -16)]

def row5 : Integer.Sparse (Fin 3237) := [(0, -1), (261, 1), (1934, 24), (1936, 6), (1950, 12), (2783, 24), (2787, 6)]

def row6 : Integer.Sparse (Fin 3237) := [(0, 26), (32, 20), (160, 320), (256, 320), (261, 10), (274, -480)]

def row7 : Integer.Sparse (Fin 3237) := [(0, 4), (261, 20), (2749, -180), (2750, -45), (2763, -180), (2766, -90)]

def row8 : Integer.Sparse (Fin 3237) := [(0, 13), (32, -15), (160, 160), (225, 160), (252, -120), (261, 120)]

def row9 : Integer.Sparse (Fin 3237) := [(0, 1), (261, -1), (2575, -36), (2578, -36), (2579, -12), (2580, -12), (2764, -72), (2769, -36)]

def row16 : Integer.Sparse (Fin 3237) := [(0, -67), (256, -80), (261, 75), (1968, 1080), (1969, 540), (1979, 540), (2742, 1080), (2766, 540), (2768, 1080), (2769, 540), (2793, 1080)]

def row17 : Integer.Sparse (Fin 3237) := [(0, 91), (256, 80), (261, 45), (1948, -1440), (1949, -720), (1950, -720), (2491, -1440), (2503, -720), (2571, -720), (2783, -1440), (2786, -1440), (2787, -720), (2791, -1440), (2794, -1440)]

def row18 : Integer.Sparse (Fin 3237) := [(0, 1115), (32, -10), (160, 160), (225, 80), (256, -240), (261, 875), (1932, -4320), (1933, -4320), (1934, -4320), (1948, -4320), (2489, -4320), (2490, -4320), (2491, -4320), (2501, -4320), (2570, -4320), (2717, -4320), (2722, -4320), (2723, -8640), (2763, -4320), (2764, -4320), (2782, -8640), (2783, -8640), (2786, -8640), (2791, -8640), (2794, -4320), (2802, -8640), (2803, -4320)]

def row19 : Integer.Sparse (Fin 3237) := [(0, -161), (256, 80), (261, -135), (1932, 1080), (1933, 1080), (1934, 1080), (1948, 1080), (2717, 1080), (2723, 1080), (2763, 1080), (2782, 1080), (2783, 1080), (2786, 1080), (2791, 1080), (2794, 1080)]

def row20 : Integer.Sparse (Fin 3237) := [(0, 220), (32, -5), (160, 80), (225, 40), (261, -245), (2726, -2160), (2727, -2160), (2729, -2160), (2741, -2160), (2742, -2160), (2762, -2160), (2764, -2160), (2765, -2160), (2768, -2160), (2793, -2160)]

def row21 : Integer.Sparse (Fin 3237) := [(0, 23), (256, -80), (261, -15), (1979, -720), (1980, -240), (2538, -720), (2579, -240), (2769, -720), (2793, -1440)]

def row22 : Integer.Sparse (Fin 3237) := [(0, 19), (261, 5), (2570, -240), (2571, -120), (2575, -240), (2794, -240), (2802, -240), (2803, -480)]

def row23 : Integer.Sparse (Fin 3237) := [(0, 174), (32, -5), (160, 80), (225, 40), (256, 160), (261, -215), (2768, -2160), (2769, -2160), (2794, -4320)]

def row24 : Integer.Sparse (Fin 3237) := [(0, 1), (261, -1), (2570, -16), (2575, -8), (2578, -8), (2762, -16), (2764, -16), (2765, -16), (2766, -8), (2768, -16), (2769, -8)]

def row25 : Integer.Sparse (Fin 3237) := [(0, -19), (261, -5), (2831, 120), (2832, 80), (2839, 240), (2840, 240)]

def row26 : Integer.Sparse (Fin 3237) := [(0, 82), (32, -55), (160, -80), (225, 40), (256, -160), (261, 155), (2693, -4320), (2698, -4320), (2802, -4320)]

def row27 : Integer.Sparse (Fin 3237) := [(0, 76), (32, -25), (160, -80), (225, -40), (256, -80), (261, 95), (2716, -540), (2717, -1080), (2722, -1080), (2762, -1080), (2791, -1080), (2802, -1080)]

def row28 : Integer.Sparse (Fin 3237) := [(0, 468), (32, -55), (160, -80), (225, -40), (256, -160), (261, 425), (2762, -2160), (2763, -2160), (2764, -4320), (2794, -2160), (2802, -6480), (2803, -4320)]

def row29 : Integer.Sparse (Fin 3237) := [(0, -53), (261, 5), (2839, 720), (2840, 360)]

def row30 : Integer.Sparse (Fin 3237) := [(698, 1), (1427, 3), (1626, 1), (1632, 1), (2833, -1)]

def row31 : Integer.Sparse (Fin 3237) := [(679, 3), (681, 1), (698, 1), (1626, 1), (2833, -1)]

def row32 : Integer.Sparse (Fin 3237) := [(679, 2), (1410, 2), (1625, 1), (1626, 1), (2833, -1)]

def row33 : Integer.Sparse (Fin 3237) := [(954, 1), (1410, 2), (1427, 2), (1626, 1), (2833, -1)]

def row34 : Integer.Sparse (Fin 3237) := [(681, 2), (954, 3), (1626, 1), (2833, -1)]

def row35 : Integer.Sparse (Fin 3237) := [(0, -27), (32, 70), (160, 80), (162, 240), (225, 80), (261, 25), (479, 4320), (481, 2160), (492, 2160), (504, 2160), (900, 4320), (913, 2160), (938, 2160), (1298, 4320), (1307, 4320), (1317, 4320), (1406, 4320), (1427, 2160), (1453, 4320), (1474, 2160), (1602, 4320), (1612, 2160), (1621, 2160), (2160, 2160), (2241, 4320)]

def row36 : Integer.Sparse (Fin 3237) := [(1603, 1), (1787, 1), (2212, 2), (2217, 1), (2574, 1), (2832, -1)]

def row37 : Integer.Sparse (Fin 3237) := [(643, 2), (645, 1), (660, 1), (674, 1), (1603, 1), (2832, -1)]

def row38 : Integer.Sparse (Fin 3237) := [(643, 1), (1382, 1), (1457, 1), (1485, 1), (1601, 1), (1603, 1), (2832, -1)]

def row39 : Integer.Sparse (Fin 3237) := [(953, 1), (1382, 1), (1395, 1), (1406, 1), (1603, 1), (2212, 1), (2832, -1)]

def row40 : Integer.Sparse (Fin 3237) := [(674, 1), (1406, 2), (1495, 1), (1603, 1), (1620, 1), (2832, -1)]

def row41 : Integer.Sparse (Fin 3237) := [(957, 1), (1457, 2), (1474, 1), (1603, 1), (2217, 1), (2832, -1)]

def row42 : Integer.Sparse (Fin 3237) := [(660, 1), (1395, 2), (1474, 1), (1603, 1), (1611, 1), (2832, -1)]

def row43 : Integer.Sparse (Fin 3237) := [(956, 1), (1485, 2), (1495, 1), (1603, 1), (1787, 1), (2832, -1)]

def row44 : Integer.Sparse (Fin 3237) := [(645, 1), (953, 2), (956, 1), (957, 1), (1603, 1), (2832, -1)]

def row45 : Integer.Sparse (Fin 3237) := [(694, 1), (1423, 2), (1625, 1), (1631, 1), (1632, 1), (2833, -1)]

def row46 : Integer.Sparse (Fin 3237) := [(678, 2), (679, 1), (680, 1), (694, 1), (1625, 1), (2833, -1)]

def row47 : Integer.Sparse (Fin 3237) := [(678, 2), (1409, 1), (1624, 1), (1625, 2), (2833, -1)]

def row48 : Integer.Sparse (Fin 3237) := [(1409, 1), (1410, 1), (1411, 1), (1423, 2), (1625, 1), (2833, -1)]

def row49 : Integer.Sparse (Fin 3237) := [(680, 2), (1411, 2), (1625, 2), (2833, -1)]

def row50 : Integer.Sparse (Fin 3237) := [(1585, 1), (2211, 1), (2214, 3), (2567, 1), (2831, -1)]

def row51 : Integer.Sparse (Fin 3237) := [(629, 1), (631, 1), (638, 3), (1585, 1), (2831, -1)]

def row52 : Integer.Sparse (Fin 3237) := [(629, 1), (1444, 3), (1583, 1), (1585, 1), (2831, -1)]

def row53 : Integer.Sparse (Fin 3237) := [(952, 1), (1379, 3), (1585, 1), (2211, 1), (2831, -1)]

def row54 : Integer.Sparse (Fin 3237) := [(638, 1), (1379, 1), (1453, 2), (1585, 1), (1593, 1), (2831, -1)]

def row55 : Integer.Sparse (Fin 3237) := [(955, 1), (1444, 1), (1453, 2), (1585, 1), (2214, 1), (2831, -1)]

def row56 : Integer.Sparse (Fin 3237) := [(631, 1), (952, 1), (955, 3), (1585, 1), (2831, -1)]

def row57 : Integer.Sparse (Fin 3237) := [(690, 1), (1419, 1), (1624, 1), (1631, 3), (2833, -1)]

def row58 : Integer.Sparse (Fin 3237) := [(0, -236), (4, -20), (32, 180), (160, 1280), (162, 320), (165, 320), (225, 640), (261, -60), (611, 17280), (614, 8640), (626, 8640), (672, 8640), (771, 17280), (781, 8640), (847, 8640), (1689, 17280), (1701, 8640), (1730, 17280), (1739, 17280), (1767, 17280), (1855, 17280), (1942, 17280), (1951, 8640), (2147, 17280), (2161, 8640)]

def row59 : Integer.Sparse (Fin 3237) := [(0, -15), (32, -5), (160, 80), (225, 80), (261, -50), (1070, 4320), (1073, 2160), (1074, 2160), (1159, 2160), (2015, 4320), (2018, 2160), (2158, 2160), (2252, 4320), (2257, 2160), (2312, 2160), (2347, 4320), (2409, 4320), (2440, 4320), (2451, 2160), (2482, 4320), (2492, 4320), (2498, 4320), (2503, 2160), (2539, 2160), (2574, 2160)]

def row60 : Integer.Sparse (Fin 3237) := [(1943, 1), (1975, 1), (2146, 2), (2160, 1), (2766, 1), (2840, -1)]

def row61 : Integer.Sparse (Fin 3237) := [(812, 2), (814, 1), (829, 1), (855, 1), (1943, 1), (2840, -1)]

def row62 : Integer.Sparse (Fin 3237) := [(855, 1), (1828, 2), (1879, 1), (1943, 1), (1974, 1), (2840, -1)]

def row63 : Integer.Sparse (Fin 3237) := [(916, 1), (1767, 2), (1786, 1), (1943, 1), (2160, 1), (2840, -1)]

def row64 : Integer.Sparse (Fin 3237) := [(812, 1), (1767, 1), (1804, 1), (1876, 1), (1941, 1), (1943, 1), (2840, -1)]

def row65 : Integer.Sparse (Fin 3237) := [(904, 1), (1804, 1), (1812, 1), (1828, 1), (1943, 1), (2146, 1), (2840, -1)]

def row66 : Integer.Sparse (Fin 3237) := [(829, 1), (1786, 1), (1812, 2), (1943, 1), (1950, 1), (2840, -1)]

def row67 : Integer.Sparse (Fin 3237) := [(944, 1), (1876, 2), (1879, 1), (1943, 1), (1975, 1), (2840, -1)]

def row68 : Integer.Sparse (Fin 3237) := [(814, 1), (904, 2), (916, 1), (944, 1), (1943, 1), (2840, -1)]

def row69 : Integer.Sparse (Fin 3237) := [(1429, 1), (2368, 2), (2375, 1), (2502, 1), (2504, 1), (2833, -1)]

def row70 : Integer.Sparse (Fin 3237) := [(1423, 2), (1427, 1), (1429, 1), (1632, 1), (2504, 1), (2833, -1)]

def row71 : Integer.Sparse (Fin 3237) := [(1632, 2), (2504, 3), (2580, 1), (2833, -1)]

def row72 : Integer.Sparse (Fin 3237) := [(2216, 1), (2372, 2), (2375, 2), (2504, 1), (2833, -1)]

def row73 : Integer.Sparse (Fin 3237) := [(1423, 2), (2372, 1), (2457, 1), (2500, 1), (2504, 1), (2833, -1)]

def row74 : Integer.Sparse (Fin 3237) := [(2210, 1), (2368, 2), (2457, 1), (2504, 2), (2833, -1)]

def row75 : Integer.Sparse (Fin 3237) := [(1427, 2), (2210, 2), (2216, 1), (2504, 1), (2833, -1)]

def row76 : Integer.Sparse (Fin 3237) := [(0, -33), (32, 5), (160, -80), (225, -80), (261, -190), (1062, 4320), (1063, 4320), (1067, 8640), (1155, 4320), (2289, 4320), (2293, 4320), (2301, 8640), (2341, 4320), (2345, 8640), (2407, 8640), (2436, 4320), (2449, 8640), (2479, 8640), (2482, 8640), (2496, 4320), (2497, 8640), (2501, 8640), (2535, 4320), (2573, 4320)]

def row77 : Integer.Sparse (Fin 3237) := [(1925, 1), (2168, 1), (2177, 1), (2182, 2), (2763, 1), (2839, -1)]

def row78 : Integer.Sparse (Fin 3237) := [(796, 1), (798, 1), (806, 2), (835, 1), (1925, 1), (2839, -1)]

def row79 : Integer.Sparse (Fin 3237) := [(835, 1), (1816, 1), (1861, 2), (1925, 1), (1958, 1), (2839, -1)]

def row80 : Integer.Sparse (Fin 3237) := [(927, 1), (1743, 1), (1758, 2), (1925, 1), (2177, 1), (2839, -1)]

def row81 : Integer.Sparse (Fin 3237) := [(796, 1), (1743, 1), (1847, 2), (1925, 1), (2839, -1)]

def row82 : Integer.Sparse (Fin 3237) := [(920, 1), (1801, 2), (1816, 1), (1925, 1), (2168, 1), (2839, -1)]

def row83 : Integer.Sparse (Fin 3237) := [(806, 1), (1758, 1), (1801, 1), (1855, 1), (1925, 1), (1934, 1), (2839, -1)]

def row84 : Integer.Sparse (Fin 3237) := [(932, 1), (1847, 1), (1855, 1), (1861, 1), (1925, 1), (2182, 1), (2839, -1)]

def row85 : Integer.Sparse (Fin 3237) := [(798, 1), (920, 1), (927, 1), (932, 2), (1925, 1), (2839, -1)]

def row86 : Integer.Sparse (Fin 3237) := [(1421, 1), (2368, 1), (2500, 1), (2502, 2), (2833, -1)]

def row87 : Integer.Sparse (Fin 3237) := [(1419, 1), (1421, 1), (1423, 2), (1631, 1), (2500, 1), (2833, -1)]

def row88 : Integer.Sparse (Fin 3237) := [(1631, 2), (2500, 2), (2580, 2), (2833, -1)]

def row89 : Integer.Sparse (Fin 3237) := [(2366, 1), (2368, 2), (2372, 2), (2500, 1), (2833, -1)]

def row90 : Integer.Sparse (Fin 3237) := [(1419, 2), (2366, 1), (2500, 3), (2833, -1)]

def row91 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (659, -120), (664, -40), (697, -40), (828, -120), (1176, -120), (1178, -40), (1179, -40), (1758, -240), (1786, -120), (2310, -120), (2320, -40), (2449, -240), (2451, -120), (2564, -120), (2575, -120), (2578, -120), (2579, -40)]

def row92 : Integer.Sparse (Fin 3237) := [(0, -4), (32, 5), (261, 5), (659, 120), (664, 40), (697, 40), (828, 120), (1758, 240), (1786, 120)]

def row93 : Integer.Sparse (Fin 3237) := [(0, 1), (32, 5), (1595, -240), (1622, -80), (1631, -240), (1632, -80), (1936, -240), (2502, -240), (2580, -120), (3171, 960), (3182, 480)]

def row94 : Integer.Sparse (Fin 3237) := [(0, -3), (32, -15), (1595, 120), (1622, 40), (1925, 240), (1936, 120), (1943, 120)]

def row95 : Integer.Sparse (Fin 3237) := [(2502, 3), (2580, 1), (2833, -1)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row151 : Integer.Sparse (Fin 3237) := [(0, 1), (32, 5), (692, -360), (700, -120), (1145, -360), (1167, -120), (1421, -720), (1429, -360), (1551, -720), (1571, -360), (1595, -360), (1622, -120), (1631, -360), (1632, -120), (1936, -360), (2502, -360), (2580, -120), (2833, 480)]

def row152 : Integer.Sparse (Fin 3237) := [(0, -1), (261, -5), (2818, 240), (2820, 30), (2829, 360), (2832, 240)]

def row153 : Integer.Sparse (Fin 3237) := [(0, -113), (32, 155), (160, -80), (162, 160), (225, 80), (261, 80), (899, 4320), (900, 4320), (901, 4320), (911, 4320), (936, 4320), (1298, 4320), (1307, 4320), (1317, 4320), (1603, 4320), (2128, 4320), (2134, 4320), (2135, 4320), (2160, 4320), (2177, 4320), (2203, 4320), (2204, 4320), (2212, 4320), (2221, 4320), (2222, 4320), (2230, 4320), (2232, 4320), (2234, 4320), (2238, 4320), (2240, 4320), (2241, 8640)]

def row154 : Integer.Sparse (Fin 3237) := [(1601, 1), (1783, 1), (2486, 1), (2532, 1), (2573, 1), (2574, 1), (2832, -1)]

def row155 : Integer.Sparse (Fin 3237) := [(642, 1), (643, 1), (644, 1), (655, 1), (671, 1), (1601, 1), (2832, -1)]

def row156 : Integer.Sparse (Fin 3237) := [(642, 1), (1456, 1), (1484, 1), (1600, 1), (1601, 2), (2832, -1)]

def row157 : Integer.Sparse (Fin 3237) := [(1382, 1), (1383, 1), (1390, 1), (1403, 1), (1601, 1), (2486, 1), (2832, -1)]

def row158 : Integer.Sparse (Fin 3237) := [(671, 1), (1403, 1), (1493, 1), (1601, 1), (1618, 1), (1620, 1), (2832, -1)]

def row159 : Integer.Sparse (Fin 3237) := [(1456, 1), (1457, 1), (1458, 1), (1469, 1), (1601, 1), (2532, 1), (2832, -1)]

def row160 : Integer.Sparse (Fin 3237) := [(655, 1), (1390, 1), (1469, 1), (1601, 1), (1610, 1), (1611, 1), (2832, -1)]

def row161 : Integer.Sparse (Fin 3237) := [(1484, 1), (1485, 1), (1486, 1), (1493, 1), (1601, 1), (1783, 1), (2832, -1)]

def row162 : Integer.Sparse (Fin 3237) := [(644, 1), (1383, 1), (1458, 1), (1486, 1), (1601, 2), (2832, -1)]

def row163 : Integer.Sparse (Fin 3237) := [(0, -40), (32, -50), (160, -400), (162, -240), (225, -160), (256, -80), (261, 70), (477, 4320), (478, 4320), (480, 4320), (489, 4320), (500, 4320), (1297, 4320), (1299, 4320), (1304, 4320), (1313, 4320), (1403, 4320), (1404, 4320), (1408, 4320), (1423, 4320), (1450, 4320), (1451, 4320), (1455, 4320), (1469, 4320), (1554, 4320), (1555, 4320), (1563, 4320), (1570, 4320), (1598, 4320), (1599, 4320), (1607, 4320), (1615, 4320), (2696, 4320), (2703, 4320), (2704, 4320)]

def row164 : Integer.Sparse (Fin 3237) := [(2241, 1), (2696, 1), (2699, 2), (2704, 2), (2840, -1)]

def row165 : Integer.Sparse (Fin 3237) := [(958, 1), (960, 2), (961, 2), (2241, 1), (2840, -1)]

def row166 : Integer.Sparse (Fin 3237) := [(958, 1), (2224, 2), (2234, 2), (2241, 1), (2840, -1)]

def row167 : Integer.Sparse (Fin 3237) := [(1747, 2), (2239, 2), (2241, 1), (2696, 1), (2840, -1)]

def row168 : Integer.Sparse (Fin 3237) := [(961, 1), (2226, 1), (2230, 1), (2236, 1), (2239, 1), (2241, 1), (2840, -1)]

def row169 : Integer.Sparse (Fin 3237) := [(1769, 1), (1928, 1), (2234, 1), (2236, 1), (2241, 1), (2704, 1), (2840, -1)]

def row170 : Integer.Sparse (Fin 3237) := [(960, 1), (1747, 1), (1759, 1), (1769, 1), (1928, 1), (2241, 1), (2840, -1)]

def row171 : Integer.Sparse (Fin 3237) := [(1583, 1), (2522, 3), (2567, 1), (2831, -1)]

def row172 : Integer.Sparse (Fin 3237) := [(629, 1), (630, 1), (635, 3), (1583, 1), (2831, -1)]

def row173 : Integer.Sparse (Fin 3237) := [(635, 1), (1450, 2), (1583, 1), (1591, 1), (1593, 1), (2831, -1)]

def row174 : Integer.Sparse (Fin 3237) := [(1444, 1), (1445, 1), (1450, 2), (1583, 1), (2522, 1), (2831, -1)]

def row175 : Integer.Sparse (Fin 3237) := [(630, 1), (1445, 3), (1583, 2), (2831, -1)]

def row176 : Integer.Sparse (Fin 3237) := [(0, -8), (32, 35), (160, 640), (162, 240), (225, 320), (256, 160), (261, -145), (464, 1440), (465, 1440), (470, 4320), (1378, 4320), (1381, 4320), (1390, 8640), (1546, 1440), (1550, 4320), (1582, 1440), (1588, 4320), (2760, 1440), (2767, 1440)]

def row177 : Integer.Sparse (Fin 3237) := [(2240, 1), (2694, 3), (2760, 1), (2797, 1), (2839, -1)]

def row178 : Integer.Sparse (Fin 3237) := [(959, 3), (962, 1), (963, 1), (2240, 1), (2839, -1)]

def row179 : Integer.Sparse (Fin 3237) := [(959, 1), (2225, 1), (2235, 1), (2238, 2), (2240, 1), (2839, -1)]

def row180 : Integer.Sparse (Fin 3237) := [(1744, 1), (2237, 1), (2238, 2), (2240, 1), (2694, 1), (2839, -1)]

def row181 : Integer.Sparse (Fin 3237) := [(962, 1), (2229, 1), (2237, 3), (2240, 1), (2839, -1)]

def row182 : Integer.Sparse (Fin 3237) := [(1922, 1), (2235, 3), (2240, 1), (2760, 1), (2839, -1)]

def row183 : Integer.Sparse (Fin 3237) := [(963, 1), (1744, 3), (1922, 1), (2240, 1), (2839, -1)]

def row184 : Integer.Sparse (Fin 3237) := [(0, -59), (32, 15), (160, -240), (162, -320), (225, -80), (261, 30), (899, 4320), (910, 1440), (2164, 1440), (2165, 1440), (2177, 4320), (2203, 4320), (2211, 1440), (2221, 4320), (2229, 1440), (2241, 8640)]

def row185 : Integer.Sparse (Fin 3237) := [(1600, 1), (1779, 1), (2531, 1), (2573, 3), (2832, -1)]

def row186 : Integer.Sparse (Fin 3237) := [(669, 1), (1491, 1), (1600, 1), (1618, 3), (2832, -1)]

def row187 : Integer.Sparse (Fin 3237) := [(1465, 1), (1600, 1), (1610, 3), (2832, -1)]

def row188 : Integer.Sparse (Fin 3237) := [(0, -31), (32, 55), (160, 80), (162, 160), (225, 80), (261, 10), (1425, 4320), (1427, 2160), (1428, 2160), (1612, 2160), (1894, 4320), (1906, 2160), (1908, 2160), (1949, 2160), (2127, 4320), (2132, 4320), (2134, 4320), (2143, 4320), (2146, 4320), (2155, 2160), (2160, 2160), (2176, 4320), (2187, 2160), (2212, 4320), (2217, 2160)]

def row189 : Integer.Sparse (Fin 3237) := [(1620, 1), (1951, 1), (2498, 2), (2574, 1), (2578, 1), (2832, -1)]

def row190 : Integer.Sparse (Fin 3237) := [(824, 2), (830, 1), (831, 1), (868, 1), (1951, 1), (2832, -1)]

def row191 : Integer.Sparse (Fin 3237) := [(868, 1), (1497, 1), (1839, 2), (1951, 1), (1978, 1), (2832, -1)]

def row192 : Integer.Sparse (Fin 3237) := [(1783, 2), (1787, 1), (1789, 1), (1951, 1), (2574, 1), (2832, -1)]

def row193 : Integer.Sparse (Fin 3237) := [(824, 1), (1493, 1), (1783, 1), (1809, 1), (1947, 1), (1951, 1), (2832, -1)]

def row194 : Integer.Sparse (Fin 3237) := [(1809, 1), (1813, 1), (1814, 1), (1839, 1), (1951, 1), (2498, 1), (2832, -1)]

def row195 : Integer.Sparse (Fin 3237) := [(831, 1), (1789, 1), (1814, 2), (1949, 1), (1951, 1), (2832, -1)]

def row196 : Integer.Sparse (Fin 3237) := [(1493, 2), (1495, 1), (1497, 1), (1620, 1), (1951, 1), (2832, -1)]

def row197 : Integer.Sparse (Fin 3237) := [(830, 1), (1495, 1), (1787, 1), (1813, 2), (1951, 1), (2832, -1)]

def row198 : Integer.Sparse (Fin 3237) := [(0, -26), (32, 5), (160, 160), (162, 80), (225, 160), (261, -85), (623, 4320), (626, 2160), (627, 2160), (694, 2160), (1699, 4320), (1701, 2160), (1702, 2160), (1738, 4320), (1739, 4320), (1740, 4320), (1783, 4320), (1942, 4320), (1943, 2160), (1944, 4320), (1946, 2160), (1978, 2160), (2528, 4320), (2538, 2160), (2539, 2160)]

def row199 : Integer.Sparse (Fin 3237) := [(0, -56), (32, -40), (160, 320), (225, 160), (255, 160), (256, 160), (261, -80), (774, 8640), (776, 4320), (782, 4320), (864, 4320), (1059, 8640), (1073, 4320), (1151, 4320), (2015, 8640), (2018, 4320), (2066, 8640), (2070, 8640), (2096, 8640), (2134, 8640), (2157, 8640), (2161, 4320), (2187, 4320), (2498, 8640), (2504, 4320), (2574, 4320)]

def row200 : Integer.Sparse (Fin 3237) := [(1973, 2), (1974, 1), (1975, 1), (1979, 1), (2766, 1), (2840, -1)]

def row201 : Integer.Sparse (Fin 3237) := [(857, 1), (942, 2), (944, 1), (948, 1), (1975, 1), (2840, -1)]

def row202 : Integer.Sparse (Fin 3237) := [(948, 1), (1963, 2), (1970, 1), (1975, 1), (2160, 1), (2840, -1)]

def row203 : Integer.Sparse (Fin 3237) := [(858, 1), (1830, 2), (1879, 1), (1974, 1), (1975, 1), (2840, -1)]

def row204 : Integer.Sparse (Fin 3237) := [(942, 1), (1829, 1), (1830, 1), (1841, 1), (1975, 1), (2146, 1), (2840, -1)]

def row205 : Integer.Sparse (Fin 3237) := [(856, 1), (1829, 1), (1876, 1), (1963, 1), (1973, 1), (1975, 1), (2840, -1)]

def row206 : Integer.Sparse (Fin 3237) := [(856, 2), (857, 1), (858, 1), (871, 1), (1975, 1), (2840, -1)]

def row207 : Integer.Sparse (Fin 3237) := [(0, -244), (4, -20), (32, 120), (160, -640), (162, -640), (165, 320), (673, 17280), (674, 8640), (675, 8640), (696, 8640), (1768, 17280), (1769, 17280), (1770, 17280), (1785, 17280), (1873, 17280), (1874, 8640), (1955, 17280), (1965, 8640), (1969, 8640), (1971, 8640), (1975, 17280), (1981, 8640), (2182, 17280)]

def row208 : Integer.Sparse (Fin 3237) := [(1842, 1), (2156, 2), (2158, 1), (2162, 1), (2537, 1), (2832, -1)]

def row209 : Integer.Sparse (Fin 3237) := [(918, 1), (2054, 1), (2111, 2), (2158, 1), (2162, 1), (2832, -1)]

def row210 : Integer.Sparse (Fin 3237) := [(1404, 1), (1840, 1), (2106, 1), (2111, 1), (2158, 1), (2497, 1), (2832, -1)]

def row211 : Integer.Sparse (Fin 3237) := [(2158, 1), (2497, 2), (2503, 1), (2537, 1), (2579, 1), (2832, -1)]

def row212 : Integer.Sparse (Fin 3237) := [(1426, 1), (2045, 2), (2054, 1), (2158, 1), (2503, 1), (2832, -1)]

def row213 : Integer.Sparse (Fin 3237) := [(0, -772), (3, 160), (4, 20), (32, -540), (66, -640), (68, -640), (160, -3200), (162, -320), (165, -320), (225, -640), (255, -1280), (256, -1280), (261, 1220), (799, 17280), (800, 17280), (808, 17280), (817, 17280), (844, 17280), (1432, 17280), (1441, 17280), (1451, 17280), (1555, 17280), (2028, 17280), (2033, 17280), (2042, 17280), (2074, 17280), (2079, 17280), (2088, 17280), (2116, 17280), (2128, 17280), (2135, 17280), (2146, 17280), (2186, 17280), (2704, 17280), (2738, 17280), (2743, 17280)]

def row214 : Integer.Sparse (Fin 3237) := [(0, -66), (32, -45), (160, -240), (162, -160), (256, -80), (261, -15), (1412, 4320), (1414, 4320), (1418, 4320), (1423, 4320), (1607, 4320), (2295, 4320), (2297, 4320), (2305, 4320), (2306, 4320), (2433, 4320), (2446, 4320), (2447, 4320), (2476, 4320), (2477, 4320), (2485, 4320), (2486, 4320), (2490, 4320), (2491, 4320), (2495, 4320), (2498, 4320), (2515, 4320), (2527, 4320), (2530, 4320), (2532, 4320), (2703, 4320), (2719, 4320), (2728, 4320)]

def row215 : Integer.Sparse (Fin 3237) := [(1935, 1), (2699, 1), (2704, 1), (2718, 1), (2743, 1), (2764, 1), (2840, -1)]

def row216 : Integer.Sparse (Fin 3237) := [(803, 1), (807, 1), (808, 1), (827, 1), (846, 1), (1935, 1), (2840, -1)]

def row217 : Integer.Sparse (Fin 3237) := [(846, 1), (1821, 1), (1870, 1), (1935, 1), (1962, 1), (1967, 1), (2840, -1)]

def row218 : Integer.Sparse (Fin 3237) := [(1754, 1), (1759, 1), (1760, 1), (1784, 1), (1935, 1), (2699, 1), (2840, -1)]

def row219 : Integer.Sparse (Fin 3237) := [(803, 1), (1754, 1), (1853, 1), (1927, 1), (1935, 1), (2840, -1)]

def row220 : Integer.Sparse (Fin 3237) := [(1802, 1), (1803, 1), (1811, 1), (1821, 1), (1935, 1), (2718, 1), (2840, -1)]

def row221 : Integer.Sparse (Fin 3237) := [(827, 1), (1784, 1), (1811, 1), (1935, 1), (1942, 1), (1948, 1), (2840, -1)]

def row222 : Integer.Sparse (Fin 3237) := [(1853, 1), (1856, 1), (1857, 1), (1870, 1), (1935, 1), (2743, 1), (2840, -1)]

def row223 : Integer.Sparse (Fin 3237) := [(808, 1), (1760, 1), (1803, 1), (1857, 1), (1933, 1), (1935, 1), (2840, -1)]

def row224 : Integer.Sparse (Fin 3237) := [(1927, 1), (1928, 1), (1935, 1), (1942, 1), (1962, 1), (2704, 1), (2840, -1)]

def row225 : Integer.Sparse (Fin 3237) := [(807, 1), (1759, 1), (1802, 1), (1856, 1), (1928, 1), (1935, 1), (2840, -1)]

def row226 : Integer.Sparse (Fin 3237) := [(0, -96), (32, 50), (160, -480), (225, -160), (255, -160), (261, -390), (1056, 8640), (1057, 8640), (1061, 8640), (1067, 8640), (1149, 8640), (1794, 8640), (1798, 8640), (1835, 8640), (1894, 8640), (2337, 8640), (2340, 8640), (2345, 8640), (2404, 8640), (2407, 8640), (2433, 8640), (2465, 8640), (2469, 8640), (2477, 8640), (2482, 8640), (2496, 8640), (2497, 8640), (2500, 8640), (2527, 8640), (2556, 8640), (2573, 8640), (2725, 8640), (2729, 8640), (2748, 8640)]

def row227 : Integer.Sparse (Fin 3237) := [(2182, 1), (2737, 1), (2742, 1), (2747, 1), (2763, 1), (2793, 1), (2839, -1)]

def row228 : Integer.Sparse (Fin 3237) := [(931, 1), (932, 1), (933, 1), (936, 1), (945, 1), (2182, 1), (2839, -1)]

def row229 : Integer.Sparse (Fin 3237) := [(936, 1), (2097, 1), (2116, 1), (2177, 1), (2182, 1), (2186, 1), (2839, -1)]

def row230 : Integer.Sparse (Fin 3237) := [(1861, 1), (2093, 1), (2125, 1), (2126, 1), (2182, 1), (2747, 1), (2839, -1)]

def row231 : Integer.Sparse (Fin 3237) := [(931, 1), (2088, 1), (2125, 1), (2168, 1), (2181, 1), (2182, 1), (2839, -1)]

def row232 : Integer.Sparse (Fin 3237) := [(1847, 1), (2092, 1), (2116, 1), (2118, 1), (2182, 1), (2737, 1), (2839, -1)]

def row233 : Integer.Sparse (Fin 3237) := [(945, 1), (2118, 1), (2126, 1), (2182, 2), (2188, 1), (2839, -1)]

def row234 : Integer.Sparse (Fin 3237) := [(1855, 1), (2088, 1), (2089, 1), (2097, 1), (2182, 1), (2742, 1), (2839, -1)]

def row235 : Integer.Sparse (Fin 3237) := [(933, 1), (2089, 1), (2092, 1), (2093, 1), (2101, 1), (2182, 1), (2839, -1)]

def row236 : Integer.Sparse (Fin 3237) := [(0, -812), (4, 20), (32, 1100), (160, -640), (162, 320), (165, -320), (261, 980), (1768, 17280), (1769, 17280), (1770, 17280), (1785, 17280), (1923, 17280), (1931, 17280), (1933, 17280), (1939, 17280), (1969, 17280), (1975, 17280), (2136, 17280), (2143, 17280), (2146, 17280), (2150, 17280), (2167, 17280), (2168, 17280), (2170, 17280), (2182, 34560), (2184, 17280), (2187, 17280), (2235, 17280), (2236, 17280)]

def row237 : Integer.Sparse (Fin 3237) := [(1835, 1), (2464, 1), (2468, 1), (2490, 1), (2497, 1), (2537, 1), (2832, -1)]

def row238 : Integer.Sparse (Fin 3237) := [(1402, 1), (1404, 1), (1408, 1), (1422, 1), (1619, 1), (2497, 1), (2832, -1)]

def row239 : Integer.Sparse (Fin 3237) := [(1619, 1), (1978, 1), (2497, 2), (2578, 1), (2579, 1), (2832, -1)]

def row240 : Integer.Sparse (Fin 3237) := [(2106, 1), (2454, 1), (2464, 1), (2497, 2), (2832, -1)]

def row241 : Integer.Sparse (Fin 3237) := [(1408, 1), (1839, 1), (2362, 1), (2454, 1), (2497, 1), (2498, 1), (2832, -1)]

def row242 : Integer.Sparse (Fin 3237) := [(2490, 1), (2496, 1), (2497, 1), (2498, 1), (2501, 1), (2578, 1), (2832, -1)]

def row243 : Integer.Sparse (Fin 3237) := [(1422, 1), (2371, 1), (2497, 1), (2501, 1), (2503, 1), (2832, -1)]

def row244 : Integer.Sparse (Fin 3237) := [(0, -772), (4, 20), (32, -480), (160, -1600), (162, -320), (165, -320), (225, -640), (255, -320), (256, -640), (261, 1040), (770, 17280), (771, 17280), (772, 17280), (779, 17280), (845, 17280), (1730, 17280), (1739, 17280), (1767, 17280), (1943, 17280), (2012, 17280), (2013, 17280), (2017, 17280), (2065, 17280), (2069, 17280), (2109, 17280), (2112, 17280), (2145, 17280), (2146, 17280), (2147, 17280), (2157, 17280), (2161, 17280), (2528, 17280), (2738, 17280)]

def row245 : Integer.Sparse (Fin 3237) := [(0, -11), (32, -5), (261, 10), (2014, 720), (2015, 720), (2016, 720), (2017, 720), (2157, 720), (2251, 720), (2252, 720), (2253, 720), (2256, 720), (2304, 720), (2409, 720), (2431, 720), (2439, 720), (2440, 720), (2448, 720), (2478, 720), (2484, 720), (2491, 720), (2492, 720), (2498, 720), (2503, 720), (2504, 720), (2514, 720), (2528, 720), (2539, 720), (2699, 720), (2718, 720)]

def row246 : Integer.Sparse (Fin 3237) := [(1941, 1), (1973, 1), (2703, 1), (2719, 1), (2765, 1), (2766, 1), (2840, -1)]

def row247 : Integer.Sparse (Fin 3237) := [(811, 1), (812, 1), (813, 1), (823, 1), (853, 1), (1941, 1), (2840, -1)]

def row248 : Integer.Sparse (Fin 3237) := [(853, 1), (1826, 1), (1878, 1), (1941, 1), (1973, 1), (1974, 1), (2840, -1)]

def row249 : Integer.Sparse (Fin 3237) := [(1765, 1), (1767, 1), (1771, 1), (1782, 1), (1941, 1), (2703, 1), (2840, -1)]

def row250 : Integer.Sparse (Fin 3237) := [(811, 1), (1765, 1), (1875, 1), (1940, 1), (1941, 2), (2840, -1)]

def row251 : Integer.Sparse (Fin 3237) := [(1804, 1), (1805, 1), (1826, 1), (1941, 1), (2719, 1), (2840, -1)]

def row252 : Integer.Sparse (Fin 3237) := [(823, 1), (1782, 1), (1941, 1), (1948, 1), (1950, 1), (2840, -1)]

def row253 : Integer.Sparse (Fin 3237) := [(1875, 1), (1876, 1), (1877, 1), (1878, 1), (1941, 1), (1973, 1), (2840, -1)]

def row254 : Integer.Sparse (Fin 3237) := [(813, 1), (1771, 1), (1805, 1), (1877, 1), (1941, 1), (1942, 1), (2840, -1)]

def row255 : Integer.Sparse (Fin 3237) := [(0, -192), (3, -40), (4, 10), (32, -90), (159, 480), (160, -1280), (162, -320), (165, -160), (225, -640), (256, -640), (261, -20), (274, 480), (608, 8640), (609, 8640), (613, 8640), (620, 8640), (670, 8640), (1686, 8640), (1687, 8640), (1691, 8640), (1697, 8640), (1729, 8640), (1732, 8640), (1736, 8640), (1765, 8640), (1822, 8640), (1852, 8640), (1858, 8640), (1890, 8640), (1915, 8640), (1921, 8640), (1940, 8640), (1941, 17280), (1947, 8640), (2746, 8640), (2748, 8640), (2749, 8640)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row1504 : Integer.Sparse (Fin 3237) := [(688, 1), (1418, 2), (1580, 1), (1623, 1), (1628, 1), (2829, -1)]

def row1505 : Integer.Sparse (Fin 3237) := [(347, -1), (572, -2), (662, -1), (691, -2), (693, -1), (1001, -1), (1121, -2), (1143, -2), (1158, -1), (1164, -1), (1424, -2), (1569, -2), (1611, -1), (1619, -1), (1620, -2), (2859, 8), (2862, 4), (2863, 4), (2875, 8), (2878, 8), (2879, 8), (2920, 8), (2922, 4), (2928, 8), (2930, 4), (2931, 4)]

def row1506 : Integer.Sparse (Fin 3237) := [(988, 2), (1001, 1), (1002, 1), (1006, 1), (1109, 2), (1121, 2), (1122, 2), (1126, 2), (1143, 2), (1149, 2), (1150, 2), (1158, 1), (1164, 1), (1166, 1), (1171, 1), (1172, 1), (1569, 2), (1619, 1), (1620, 1)]

def row1507 : Integer.Sparse (Fin 3237) := [(0, 3), (4, 1), (66, -16), (261, 12), (490, -864), (499, -864), (503, -432), (506, -432), (518, -432), (519, -432), (622, -864), (657, -864), (693, -432), (695, -432), (866, -432), (1069, -864), (1158, -432), (1163, -864), (1165, -432), (2315, -432), (2318, -432), (2897, 3456), (2905, 3456), (2906, 3456), (2920, 3456), (2921, 3456), (2937, 1728), (2938, 1728), (2939, 1728), (2968, 3456), (2972, 1728)]

def row1508 : Integer.Sparse (Fin 3237) := [(342, -1), (567, -2), (691, -2), (693, -2), (695, -1), (697, -1), (995, -1), (1115, -2), (1143, -2), (1158, -2), (1165, -1), (1179, -1), (1422, -2), (1562, -2), (1611, -1), (1619, -1), (2858, 8), (2860, 4), (2863, 4), (2876, 8), (2879, 8), (2927, 8), (2929, 4), (2931, 4)]

def row1509 : Integer.Sparse (Fin 3237) := [(984, 2), (995, 1), (996, 1), (1002, 1), (1115, 2), (1116, 2), (1122, 2), (1143, 2), (1144, 2), (1158, 2), (1159, 1), (1165, 1), (1166, 1), (1179, 1), (1562, 2), (1611, 1)]

def row1510 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -25), (160, -80), (261, 80), (292, -4320), (293, -2160), (294, -2160), (298, -2160), (389, -4320), (390, -2160), (391, -2160), (404, -2160), (534, -4320), (535, -4320), (536, -4320), (540, -4320), (622, -4320), (625, -2160), (628, -2160), (654, -4320), (656, -2160), (663, -2160), (691, -4320), (692, -2160), (693, -2160), (1023, -4320), (1024, -4320), (1025, -4320), (1036, -4320), (1069, -4320), (1072, -2160), (1075, -2160), (1143, -4320), (1145, -2160), (1156, -4320), (1157, -2160), (1158, -2160), (1177, -2160), (1782, -4320), (1950, -2160), (2439, -4320), (2503, -2160), (2571, -2160), (2575, -2160)]

def row1511 : Integer.Sparse (Fin 3237) := [(0, 19), (4, 5), (71, -80), (261, -40), (488, -8640), (491, -2160), (517, -2160), (619, -4320), (622, -4320), (654, -4320), (687, -2160), (695, -2160), (866, -2160), (1054, -4320), (1069, -4320), (1097, -2160), (1156, -4320), (1165, -2160), (2315, -2160), (2319, -2160), (2904, 17280), (2919, 17280), (2920, 17280), (2935, 8640), (2937, 8640), (2967, 17280), (2973, 8640)]

def row1512 : Integer.Sparse (Fin 3237) := [(687, 1), (1417, 2), (1617, 1), (1629, 1), (2830, -1)]

def row1513 : Integer.Sparse (Fin 3237) := [(337, -2), (345, -1), (348, -2), (563, -2), (570, -2), (573, -4), (654, -4), (659, -2), (663, -2), (993, -2), (1011, -1), (1012, -2), (1113, -2), (1130, -2), (1131, -4), (1156, -4), (1176, -2), (1177, -2), (2831, 4)]

def row1514 : Integer.Sparse (Fin 3237) := [(334, -2), (339, -1), (342, -1), (347, -1), (561, -2), (565, -2), (567, -2), (572, -2), (653, -2), (656, -1), (662, -1), (691, -2), (693, -1), (695, -1), (983, -2), (994, -1), (995, -1), (1001, -1), (1106, -2), (1114, -2), (1115, -2), (1121, -2), (1142, -2), (1143, -2), (1157, -1), (1158, -1), (1164, -1), (1165, -1), (2832, 4)]

def row1515 : Integer.Sparse (Fin 3237) := [(686, 1), (1416, 2), (1609, 1), (1628, 1), (2829, -1)]

def row1516 : Integer.Sparse (Fin 3237) := [(336, -1), (562, -2), (692, -4), (700, -2), (985, -1), (1107, -2), (1145, -4), (1167, -2), (1421, -2), (1551, -2), (1595, -1), (1631, -1), (2857, 8), (2861, 8), (2877, 16), (2936, 8), (2937, 8)]

def row1517 : Integer.Sparse (Fin 3237) := [(0, -106), (3, -40), (32, -520), (68, -160), (261, 10), (378, 2160), (379, 2160), (897, 4320), (947, 2160), (948, 2160)]

def row1518 : Integer.Sparse (Fin 3237) := [(979, 2), (985, 1), (989, 2), (1107, 2), (1110, 4), (1138, 2), (1145, 4), (1151, 2), (1167, 2), (1551, 2), (1595, 1)]

def row1519 : Integer.Sparse (Fin 3237) := [(332, 2), (336, 1), (341, 2), (692, 1), (2833, -1)]

def row1520 : Integer.Sparse (Fin 3237) := [(332, 1), (690, 1), (692, 3), (2833, -1)]

def row1521 : Integer.Sparse (Fin 3237) := [(0, -106), (3, 200), (4, -60), (32, 80), (68, -160), (261, -50), (837, 2160), (849, 2160), (850, 2160), (871, 2160), (939, 4320)]

def row1522 : Integer.Sparse (Fin 3237) := [(623, 1), (1329, 1), (1371, 1), (1563, 1), (1574, 1), (1577, 1), (2829, -1)]

def row1523 : Integer.Sparse (Fin 3237) := [(620, 1), (1328, 1), (1369, 1), (1573, 1), (1577, 1), (1580, 1), (2829, -1)]

def row1524 : Integer.Sparse (Fin 3237) := [(624, 1), (1330, 1), (1372, 1), (1570, 2), (1578, 1), (2830, -1)]

def row1525 : Integer.Sparse (Fin 3237) := [(619, 2), (624, 1), (683, 1), (1578, 1), (2830, -1)]

def row1526 : Integer.Sparse (Fin 3237) := [(622, 1), (1370, 1), (1562, 1), (1569, 1), (2828, -1)]

def row1527 : Integer.Sparse (Fin 3237) := [(617, 1), (622, 2), (685, 1), (2828, -1)]

def row1528 : Integer.Sparse (Fin 3237) := [(619, 1), (1368, 1), (1568, 1), (1578, 1), (2830, -1)]

def row1529 : Integer.Sparse (Fin 3237) := [(533, 1), (535, 1), (539, 1), (619, 1), (2830, -1)]

def row1530 : Integer.Sparse (Fin 3237) := [(618, 1), (1367, 1), (1561, 1), (1577, 1), (2829, -1)]

def row1531 : Integer.Sparse (Fin 3237) := [(472, 1), (1082, 2), (1137, 2), (1141, 1), (2816, -1)]

def row1532 : Integer.Sparse (Fin 3237) := [(469, 2), (472, 1), (1141, 1), (2816, -1)]

def row1533 : Integer.Sparse (Fin 3237) := [(290, 1), (486, 2), (497, 1), (2817, -1)]

def row1534 : Integer.Sparse (Fin 3237) := [(469, 1), (1080, 2), (1141, 1), (1143, 1), (2816, -1)]

def row1535 : Integer.Sparse (Fin 3237) := [(277, 1), (430, 1), (469, 2), (2816, -1)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row1536 : Integer.Sparse (Fin 3237) := [(277, -1), (282, -1), (284, -2), (385, -1), (397, -1), (398, -2), (411, -1), (413, -2), (430, -1), (435, -1), (437, -2), (454, -1), (455, -2), (469, -2), (473, -2), (475, -2), (482, -1), (486, -2), (508, -1), (509, -2), (514, -2), (515, -2), (617, -1), (685, -1), (691, -2), (1049, -1), (1092, -1), (1143, -2), (2816, 4)]

def row1537 : Integer.Sparse (Fin 3237) := [(385, 1), (397, 1), (398, 2), (454, 1), (455, 2), (482, 1), (486, 2), (508, 1), (509, 2), (514, 2), (515, 2), (617, 1), (685, 1), (691, 2), (2816, 1)]

def row1538 : Integer.Sparse (Fin 3237) := [(430, 1), (435, 1), (437, 2), (1092, 1), (2816, -1)]

def row1539 : Integer.Sparse (Fin 3237) := [(290, -1), (292, -2), (295, -1), (383, -1), (389, -2), (395, -1), (419, -2), (422, -1), (447, -2), (452, -1), (469, -2), (472, -1), (486, -2), (488, -4), (490, -4), (497, -1), (499, -4), (502, -2), (600, -1), (654, -2), (657, -1), (1064, -1), (1156, -2), (1163, -1), (2817, 4)]

def row1540 : Integer.Sparse (Fin 3237) := [(2805, 2), (2806, 1), (2807, 2), (2811, 2), (2812, 2), (2813, 4), (2816, 2), (2817, 6), (2818, 2), (2819, 2), (2828, 2), (2831, 1), (2832, 2)]

def row1541 : Integer.Sparse (Fin 3237) := [(1138, 1), (2163, 1), (2173, 3), (2314, 1), (2816, -1)]

def row1542 : Integer.Sparse (Fin 3237) := [(1138, 1), (1143, 3), (2314, 1), (2816, -1)]

def row1543 : Integer.Sparse (Fin 3237) := [(331, 1), (669, 1), (691, 3), (2832, -1)]

def row1544 : Integer.Sparse (Fin 3237) := [(2296, 3), (2302, 1), (2314, 1), (2816, -1)]

def row1545 : Integer.Sparse (Fin 3237) := [(1137, 1), (1141, 3), (2302, 1), (2816, -1)]

def row1546 : Integer.Sparse (Fin 3237) := [(876, 3), (879, 1), (910, 1), (2046, 1), (2839, -1)]

def row1547 : Integer.Sparse (Fin 3237) := [(1137, 1), (2249, 3), (2254, 1), (2302, 1), (2816, -1)]

def row1548 : Integer.Sparse (Fin 3237) := [(839, 1), (1864, 1), (1895, 1), (1954, 3), (2835, -1)]

def row1549 : Integer.Sparse (Fin 3237) := [(1088, 1), (2163, 1), (2299, 3), (2314, 1), (2816, -1)]

def row1550 : Integer.Sparse (Fin 3237) := [(730, 1), (731, 1), (734, 2), (819, 1), (1780, 1), (2840, -1)]

def row1551 : Integer.Sparse (Fin 3237) := [(371, 1), (821, 1), (843, 3), (865, 1), (2839, -1)]

def row1552 : Integer.Sparse (Fin 3237) := [(1080, 2), (1082, 1), (1088, 1), (1141, 1), (2299, 1), (2816, -1)]

def row1553 : Integer.Sparse (Fin 3237) := [(1045, 1), (1049, 2), (1143, 1), (2299, 1), (2816, -1)]

def row1554 : Integer.Sparse (Fin 3237) := [(1143, 1), (2299, 1), (2313, 2), (2314, 1), (2317, 1), (2816, -1)]

def row1555 : Integer.Sparse (Fin 3237) := [(1049, 1), (2249, 1), (2296, 1), (2299, 2), (2302, 1), (2816, -1)]

def row1556 : Integer.Sparse (Fin 3237) := [(1141, 1), (2299, 2), (2302, 2), (2317, 1), (2816, -1)]

def row1557 : Integer.Sparse (Fin 3237) := [(1092, 1), (2173, 1), (2296, 1), (2313, 2), (2314, 1), (2816, -1)]

def row1558 : Integer.Sparse (Fin 3237) := [(1080, 1), (1083, 1), (1085, 1), (1092, 1), (1143, 1), (2313, 1), (2816, -1)]

def row1559 : Integer.Sparse (Fin 3237) := [(0, 34), (4, 5), (32, 5), (66, -80), (160, -80), (261, 170), (326, -720), (327, -2160), (344, -720), (726, -2160), (739, -720), (777, -720), (778, -2160), (865, -2160), (866, -4320), (973, -720), (974, -2160), (1000, -720), (2159, -720), (2254, -720), (2255, -2160), (2263, -2160), (2279, -720), (2314, -2160), (2315, -4320), (2318, -2160), (2567, -720), (2571, -2160)]

def row1560 : Integer.Sparse (Fin 3237) := [(0, -34), (4, -5), (32, -5), (66, 80), (160, 80), (261, -170), (326, 720), (327, 2160), (344, 720), (726, 2160), (739, 720), (777, 720), (778, 2160), (865, 2160), (866, 4320), (2159, 720)]

def row1561 : Integer.Sparse (Fin 3237) := [(821, -1), (826, -3), (1836, -1), (1968, -3), (2302, -1), (2309, -3), (2518, -1), (2536, -3), (2856, 4), (2857, 4), (2858, 12), (2951, 4), (2952, 12), (2965, 12), (2966, 12), (2967, 24)]

def row1562 : Integer.Sparse (Fin 3237) := [(0, -80), (3, 40), (4, -15), (32, 25), (66, 240), (68, 160), (160, 240), (261, -100), (331, 2160), (332, 2160), (335, 6480), (729, 2160), (731, 6480), (819, 6480), (820, 6480), (823, 12960)]

def row1563 : Integer.Sparse (Fin 3237) := [(978, 1), (979, 1), (984, 3), (1911, 1), (1917, 3), (2267, 3), (2299, 3), (2302, 1), (2304, 6), (2309, 3), (2518, 1), (2536, 3)]

def row1564 : Integer.Sparse (Fin 3237) := [(371, 1), (374, 3), (378, 1), (865, 1), (2839, -1)]

def row1565 : Integer.Sparse (Fin 3237) := [(0, -75), (3, -20), (4, 25), (32, 65), (66, -80), (68, -80), (71, -160), (160, -80), (165, -160), (261, 115), (648, 1440), (685, 4320), (815, 4320), (821, 1440), (839, 1440), (843, 4320), (859, 4320), (863, 8640), (947, 1440)]

def row1566 : Integer.Sparse (Fin 3237) := [(1088, 1), (1092, 3), (2314, 1), (2816, -1)]

def row1567 : Integer.Sparse (Fin 3237) := [(0, 143), (4, 15), (66, -80), (71, -160), (261, -110), (333, -1440), (334, -2880), (337, -2880), (730, -2880), (733, -2880), (821, -2880), (822, -5760), (826, -2880), (982, -1440), (983, -2880), (993, -2880), (2266, -2880), (2273, -2880), (2302, -2880), (2303, -5760), (2309, -2880), (2317, -2880), (2318, -2880), (2319, -5760), (2553, -1440), (2570, -2880)]

def row1568 : Integer.Sparse (Fin 3237) := [(0, -143), (4, -15), (66, 80), (71, 160), (261, 110), (333, 1440), (334, 2880), (337, 2880), (730, 2880), (733, 2880), (821, 2880), (822, 5760), (826, 2880)]

def row1569 : Integer.Sparse (Fin 3237) := [(0, 37), (4, -15), (66, 80), (71, 160), (261, -70), (652, -2160), (691, -4320), (821, -4320), (865, -4320), (1141, -2160), (1143, -4320), (2302, -4320), (2314, -4320), (2317, -4320), (2965, 17280), (2971, 17280)]

def row1570 : Integer.Sparse (Fin 3237) := [(815, 1), (1775, 1), (1918, 1), (1930, 2), (1938, 1), (2838, -1)]

def row1571 : Integer.Sparse (Fin 3237) := [(733, -3), (739, -1), (826, -3), (865, -1), (1932, -3), (2273, -3), (2279, -1), (2309, -3), (2314, -1), (2489, -3), (2841, 4), (2842, 12), (2856, 4), (2959, 12), (2960, 24), (2965, 12)]

def row1572 : Integer.Sparse (Fin 3237) := [(0, -203), (1, 320), (2, -20), (32, 155), (34, 480), (35, 160), (37, 960), (160, 1200), (255, 480), (256, 480), (261, -970), (311, 4320), (312, 12960), (331, 4320), (801, 12960), (802, 25920), (819, 12960)]

def row1573 : Integer.Sparse (Fin 3237) := [(977, 1), (978, 1), (980, 3), (2273, 3), (2279, 1), (2298, 3), (2299, 3), (2300, 6), (2309, 3), (2314, 1), (2489, 3)]

def row1574 : Integer.Sparse (Fin 3237) := [(359, 3), (363, 1), (371, 1), (821, 1), (2839, -1)]

def row1575 : Integer.Sparse (Fin 3237) := [(0, 84), (4, -15), (32, 55), (66, 80), (71, 160), (160, 80), (261, -90), (301, -4320), (305, -1440), (333, -1440), (701, -4320), (704, -1440), (790, -4320), (821, -1440), (822, -8640), (826, -4320), (964, -4320), (967, -1440), (982, -1440), (2046, -1440), (2242, -4320), (2244, -1440), (2291, -4320), (2302, -1440), (2303, -8640), (2309, -4320), (2317, -4320), (2566, -1440), (2570, -4320)]

def row1576 : Integer.Sparse (Fin 3237) := [(0, -84), (4, 15), (32, -55), (66, -80), (71, -160), (160, -80), (261, 90), (301, 4320), (305, 1440), (333, 1440), (701, 4320), (704, 1440), (790, 4320), (821, 1440), (822, 8640), (826, 4320), (2046, 1440)]

def row1577 : Integer.Sparse (Fin 3237) := [(773, 1), (1694, 1), (1893, 2), (1900, 1), (1907, 1), (2836, -1)]

def row1578 : Integer.Sparse (Fin 3237) := [(777, 1), (1895, 4), (2835, -1)]

def row1579 : Integer.Sparse (Fin 3237) := [(704, 4), (777, 1), (2835, -1)]

def row1580 : Integer.Sparse (Fin 3237) := [(665, 1), (1487, 1), (1567, 1), (1598, 2), (1616, 1), (2828, -1)]

def row1581 : Integer.Sparse (Fin 3237) := [(646, 1), (1459, 1), (1560, 1), (1588, 1), (1598, 1), (1608, 1), (2828, -1)]

def row1582 : Integer.Sparse (Fin 3237) := [(648, 1), (1461, 1), (1589, 3), (2827, -1)]

def row1583 : Integer.Sparse (Fin 3237) := [(430, 3), (434, 1), (1088, 1), (2816, -1)]

def row1584 : Integer.Sparse (Fin 3237) := [(333, -1), (652, -2), (654, -4), (657, -2), (982, -1), (1141, -2), (1156, -4), (1163, -2), (1466, -1), (1589, -1), (1591, -4), (2842, 8), (2844, 8), (2883, 8), (2885, 8), (2910, 16)]

def row1585 : Integer.Sparse (Fin 3237) := [(980, 2), (982, 1), (986, 2), (1139, 2), (1141, 2), (1146, 2), (1148, 4), (1156, 4), (1163, 2), (1589, 1), (1591, 2)]

def row1586 : Integer.Sparse (Fin 3237) := [(333, 1), (652, 3), (2831, -1)]

def row1587 : Integer.Sparse (Fin 3237) := [(0, 143), (4, 15), (66, -80), (71, -160), (261, -110), (275, -8640), (277, -8640), (290, -4320), (381, -8640), (383, -4320), (385, -8640), (561, -8640), (563, -8640), (598, -17280), (600, -8640), (617, -8640), (653, -8640), (654, -17280), (691, -8640), (1047, -17280), (1049, -8640), (1064, -8640), (1106, -8640), (1113, -8640), (1142, -8640), (1143, -8640), (1156, -17280), (1932, -8640), (2489, -8640), (2553, -4320), (2570, -8640)]

def row1588 : Integer.Sparse (Fin 3237) := [(0, -143), (4, -15), (66, 80), (71, 160), (261, 110), (275, 8640), (277, 8640), (290, 4320), (561, 8640), (563, 8640), (598, 17280), (600, 8640), (617, 8640), (653, 8640), (654, 17280), (691, 8640), (1932, 8640)]

def row1589 : Integer.Sparse (Fin 3237) := [(0, 37), (4, -15), (66, 80), (71, 160), (261, -70), (469, -8640), (472, -4320), (486, -8640), (497, -4320), (648, -8640), (652, -17280), (691, -8640), (821, -8640), (1088, -8640), (1141, -17280), (1143, -8640), (2302, -8640), (2317, -4320), (2917, 69120), (2923, 34560), (2926, 34560), (2965, 34560)]

def row1590 : Integer.Sparse (Fin 3237) := [(682, 1), (1412, 1), (1573, 1), (1577, 1), (1607, 1), (1628, 1), (2829, -1)]

def row1591 : Integer.Sparse (Fin 3237) := [(683, 1), (1413, 1), (1578, 1), (1615, 2), (1629, 1), (2830, -1)]

def row1592 : Integer.Sparse (Fin 3237) := [(685, 1), (1415, 1), (1608, 2), (1616, 1), (2828, -1)]

def row1593 : Integer.Sparse (Fin 3237) := [(334, -1), (561, -1), (653, -1), (691, -2), (693, -2), (695, -2), (983, -1), (1106, -1), (1142, -1), (1143, -2), (1158, -2), (1165, -2), (1420, -1), (1549, -1), (1592, -1), (1593, -1), (1610, -1), (1618, -1), (2856, 4), (2858, 4), (2859, 8), (2875, 8), (2920, 8), (2926, 4), (2927, 4), (2928, 8)]

def row1594 : Integer.Sparse (Fin 3237) := [(978, 1), (983, 1), (984, 1), (988, 2), (1106, 1), (1109, 2), (1137, 1), (1142, 1), (1143, 2), (1144, 1), (1149, 2), (1150, 2), (1158, 2), (1165, 2), (1549, 1), (1592, 1), (1593, 1)]

def row1595 : Integer.Sparse (Fin 3237) := [(333, -1), (337, -3), (344, -1), (563, -3), (569, -1), (652, -3), (654, -6), (657, -3), (982, -1), (993, -3), (1000, -1), (1113, -3), (1120, -1), (1141, -3), (1156, -6), (1163, -3), (2831, 4)]

def row1596 : Integer.Sparse (Fin 3237) := [(615, 1), (1325, 1), (1559, 1), (1572, 1), (1577, 2), (2829, -1)]

def row1597 : Integer.Sparse (Fin 3237) := [(1326, 1), (1566, 2), (1578, 2), (2830, -1)]

def row1598 : Integer.Sparse (Fin 3237) := [(305, -4), (326, -1), (600, -12), (648, -4), (967, -4), (973, -1), (1064, -12), (1088, -4), (2827, 4)]

def row1599 : Integer.Sparse (Fin 3237) := [(277, -3), (281, -1), (385, -3), (392, -1), (430, -3), (434, -1), (469, -6), (472, -3), (482, -3), (486, -6), (494, -1), (497, -3), (648, -1), (652, -3), (1088, -1), (1141, -3), (2816, 4)]

def row1600 : Integer.Sparse (Fin 3237) := [(2804, 1), (2805, 4), (2811, 4), (2816, 4), (2817, 12), (2827, 1), (2831, 4)]

def row1601 : Integer.Sparse (Fin 3237) := [(580, 1), (1232, 1), (1346, 2), (1427, 1), (1429, 1), (2833, -1)]

def row1602 : Integer.Sparse (Fin 3237) := [(1573, 2), (1575, 1), (1580, 1), (1623, 1), (1628, 1), (2829, -1)]

def row1603 : Integer.Sparse (Fin 3237) := [(571, 1), (1225, 1), (1341, 1), (1395, 1), (1406, 1), (1424, 1), (2832, -1)]

def row1604 : Integer.Sparse (Fin 3237) := [(557, 1), (1210, 1), (1335, 1), (1355, 1), (1395, 1), (1397, 1), (2832, -1)]

def row1605 : Integer.Sparse (Fin 3237) := [(589, 1), (1240, 1), (1351, 1), (1453, 2), (1471, 1), (2831, -1)]

def row1606 : Integer.Sparse (Fin 3237) := [(1572, 1), (1573, 2), (1574, 1), (1577, 2), (2829, -1)]

def row1607 : Integer.Sparse (Fin 3237) := [(566, 1), (1220, 1), (1338, 1), (1404, 1), (1422, 1), (1426, 1), (2832, -1)]

def row1608 : Integer.Sparse (Fin 3237) := [(741, 1), (1656, 1), (1714, 1), (1759, 1), (1769, 1), (1784, 1), (2840, -1)]

def row1609 : Integer.Sparse (Fin 3237) := [(1329, 1), (1563, 1), (2347, 1), (2409, 1), (2440, 1), (2449, 1), (2829, -1)]

def row1610 : Integer.Sparse (Fin 3237) := [(1304, 1), (1307, 1), (1308, 1), (1329, 1), (1563, 1), (2440, 1), (2829, -1)]

def row1611 : Integer.Sparse (Fin 3237) := [(1559, 1), (1561, 1), (1563, 1), (1577, 1), (1607, 1), (2449, 1), (2829, -1)]

def row1612 : Integer.Sparse (Fin 3237) := [(549, 1), (1203, 1), (1348, 1), (1378, 1), (1389, 1), (1394, 1), (2831, -1)]

def row1613 : Integer.Sparse (Fin 3237) := [(720, 1), (1641, 1), (1723, 1), (1744, 2), (1756, 1), (2839, -1)]

def row1614 : Integer.Sparse (Fin 3237) := [(1325, 1), (1559, 1), (2341, 1), (2436, 1), (2449, 2), (2829, -1)]

def row1615 : Integer.Sparse (Fin 3237) := [(552, 1), (1206, 1), (1351, 1), (1379, 2), (1392, 1), (2831, -1)]

def row1616 : Integer.Sparse (Fin 3237) := [(1298, 1), (1299, 1), (1305, 1), (1315, 1), (1554, 1), (2434, 1), (2828, -1)]

def row1617 : Integer.Sparse (Fin 3237) := [(594, 1), (1244, 1), (1355, 2), (1474, 1), (1476, 1), (2832, -1)]

def row1618 : Integer.Sparse (Fin 3237) := [(585, 1), (1237, 1), (1348, 1), (1451, 1), (1468, 1), (1473, 1), (2831, -1)]

def row1619 : Integer.Sparse (Fin 3237) := [(725, 1), (1645, 1), (1707, 1), (1726, 1), (1759, 1), (1760, 1), (2840, -1)]

def row1620 : Integer.Sparse (Fin 3237) := [(1328, 1), (1607, 1), (2345, 1), (2407, 1), (2449, 1), (2451, 1), (2829, -1)]

def row1621 : Integer.Sparse (Fin 3237) := [(1607, 2), (1609, 1), (1612, 1), (1628, 1), (2451, 1), (2829, -1)]

def row1622 : Integer.Sparse (Fin 3237) := [(1313, 1), (1317, 1), (1318, 1), (1330, 1), (1570, 1), (2448, 1), (2830, -1)]

def row1623 : Integer.Sparse (Fin 3237) := [(750, 1), (1662, 1), (1719, 2), (1787, 1), (1789, 1), (2832, -1)]

def row1624 : Integer.Sparse (Fin 3237) := [(1331, 1), (1612, 1), (2015, 2), (2018, 1), (2451, 1), (2829, -1)]

def row1625 : Integer.Sparse (Fin 3237) := [(736, 1), (1652, 1), (1710, 1), (1767, 1), (1782, 1), (1786, 1), (2840, -1)]

def row1626 : Integer.Sparse (Fin 3237) := [(1308, 1), (2334, 1), (2350, 1), (2364, 1), (2438, 1), (2440, 1), (2829, -1)]

def row1627 : Integer.Sparse (Fin 3237) := [(2436, 1), (2438, 2), (2440, 1), (2449, 2), (2829, -1)]

def row1628 : Integer.Sparse (Fin 3237) := [(716, 1), (1639, 1), (1721, 1), (1743, 1), (1753, 1), (1758, 1), (2839, -1)]

def row1629 : Integer.Sparse (Fin 3237) := [(1302, 1), (2413, 1), (2436, 1), (2438, 2), (2829, -1)]

def row1630 : Integer.Sparse (Fin 3237) := [(877, 1), (1710, 1), (1718, 1), (1786, 1), (1812, 1), (2047, 1), (2840, -1)]

def row1631 : Integer.Sparse (Fin 3237) := [(759, 1), (1668, 1), (1718, 1), (1790, 1), (1812, 1), (1815, 1), (2840, -1)]

def row1632 : Integer.Sparse (Fin 3237) := [(895, 1), (1721, 1), (1725, 1), (1758, 1), (1855, 1), (2097, 1), (2839, -1)]

def row1633 : Integer.Sparse (Fin 3237) := [(1416, 1), (2364, 1), (2413, 1), (2438, 1), (2482, 1), (2488, 1), (2829, -1)]

def row1634 : Integer.Sparse (Fin 3237) := [(1369, 1), (1374, 1), (1376, 1), (1418, 1), (1580, 1), (2482, 1), (2829, -1)]

def row1635 : Integer.Sparse (Fin 3237) := [(2438, 2), (2479, 1), (2482, 2), (2564, 1), (2829, -1)]

def row1636 : Integer.Sparse (Fin 3237) := [(1376, 1), (2334, 1), (2343, 1), (2438, 1), (2482, 1), (2829, -1)]

def row1637 : Integer.Sparse (Fin 3237) := [(1479, 1), (1481, 1), (1483, 1), (1489, 1), (1569, 1), (1944, 1), (2828, -1)]

def row1638 : Integer.Sparse (Fin 3237) := [(752, 1), (1663, 1), (1709, 1), (1755, 1), (1808, 1), (2840, -1)]

def row1639 : Integer.Sparse (Fin 3237) := [(2405, 1), (2407, 1), (2409, 1), (2449, 1), (2479, 1), (2829, -1)]

def row1640 : Integer.Sparse (Fin 3237) := [(1358, 1), (1360, 1), (1367, 1), (1384, 1), (1561, 1), (2829, -1)]

def row1641 : Integer.Sparse (Fin 3237) := [(1367, 1), (2350, 1), (2405, 1), (2438, 1), (2479, 1), (2829, -1)]

def row1642 : Integer.Sparse (Fin 3237) := [(1561, 1), (2438, 1), (2449, 1), (2488, 1), (2558, 1), (2829, -1)]

def row1643 : Integer.Sparse (Fin 3237) := [(887, 1), (1706, 1), (1713, 1), (1758, 1), (1801, 1), (2081, 1), (2839, -1)]

def row1644 : Integer.Sparse (Fin 3237) := [(754, 1), (1665, 1), (1713, 1), (1801, 2), (1810, 1), (2839, -1)]

def row1645 : Integer.Sparse (Fin 3237) := [(1432, 1), (1434, 1), (1438, 1), (1447, 1), (1549, 1), (2513, 1), (2827, -1)]

def row1646 : Integer.Sparse (Fin 3237) := [(1730, 1), (1732, 1), (1737, 1), (1763, 1), (1915, 1), (2690, 1), (2838, -1)]

def row1647 : Integer.Sparse (Fin 3237) := [(1363, 1), (1365, 1), (1370, 1), (1400, 1), (1569, 1), (2477, 1), (2828, -1)]

def row1648 : Integer.Sparse (Fin 3237) := [(0, 53), (3, -20), (4, -5), (261, 260), (740, -2160), (744, -540), (749, -1080), (1999, -2160), (2004, -540), (2283, -2160), (2285, -540), (2287, -1080), (2320, -1080), (2543, -2160), (2549, -540), (2554, -2160), (2558, -2160), (2563, -1080)]

def row1649 : Integer.Sparse (Fin 3237) := [(0, -53), (3, 20), (4, 5), (261, -260), (740, 2160), (744, 540), (749, 1080), (1999, 2160), (2004, 540)]

def row1650 : Integer.Sparse (Fin 3237) := [(0, 19), (3, -4), (4, -1), (261, -14), (565, -864), (568, -216), (578, -432), (656, -432), (1114, -864), (1117, -216), (1133, -432), (1157, -432), (1651, -864), (1660, -216), (1709, -432), (1755, -864), (1936, -216), (2387, -864), (2398, -216), (2419, -432), (2438, -864), (2502, -216), (2557, -864), (2565, -432), (2575, -432)]

def row1651 : Integer.Sparse (Fin 3237) := [(0, -19), (3, 4), (4, 1), (261, 14), (565, 864), (568, 216), (578, 432), (656, 432), (1651, 864), (1660, 216), (1709, 432), (1755, 864), (1936, 216)]

def row1652 : Integer.Sparse (Fin 3237) := [(0, 71), (3, -20), (4, -5), (32, 30), (261, -40), (570, -1440), (574, -720), (579, -720), (659, -720), (735, -1440), (748, -720), (1130, -1440), (1132, -720), (1134, -720), (1176, -720), (1655, -1440), (1661, -720), (1713, -1440), (1718, -1440), (1758, -1440), (2274, -1440), (2286, -720), (2320, -720), (2396, -1440), (2399, -720), (2425, -1440), (2427, -1440), (2449, -1440), (2557, -1440), (2562, -1440), (2563, -720), (2564, -1440), (2565, -720), (2578, -720), (2580, -720)]

def row1653 : Integer.Sparse (Fin 3237) := [(0, -71), (3, 20), (4, 5), (32, -30), (261, 40), (570, 1440), (574, 720), (579, 720), (659, 720), (735, 1440), (748, 720), (1655, 1440), (1661, 720), (1713, 1440), (1718, 1440), (1758, 1440)]

def row1654 : Integer.Sparse (Fin 3237) := [(0, 19), (3, 20), (4, 5), (261, 100), (1394, -4320), (1426, -2160), (1473, -2160), (1577, -4320), (1580, -2160), (1628, -2160), (1755, -4320), (1758, -4320), (1786, -2160), (2438, -4320), (2449, -4320), (2451, -2160), (2558, -2160), (3122, 8640), (3126, 17280)]

def row1655 : Integer.Sparse (Fin 3237) := [(0, 45), (3, -20), (32, -5), (66, -80), (160, 80), (225, -80), (261, 150), (435, -4320), (438, -2160), (441, -2160), (503, -2160), (508, -4320), (510, -2160), (512, -2160), (518, -2160), (727, -4320), (747, -2160), (869, -2160), (1224, -4320), (1231, -2160), (1276, -4320), (1280, -4320), (1316, -4320), (1320, -4320), (1322, -4320), (1324, -4320), (1329, -4320), (1471, -4320), (1473, -4320), (1476, -2160), (1524, -4320), (1526, -2160), (1528, -2160), (1616, -4320), (1617, -2160), (1620, -4320), (1622, -2160), (1628, -4320), (1630, -2160), (1632, -2160), (2097, -4320), (2556, -4320), (2563, -2160), (2579, -2160), (2766, -2160)]

def row1656 : Integer.Sparse (Fin 3237) := [(0, -45), (3, 20), (32, 5), (66, 80), (160, -80), (225, 80), (261, -150), (435, 4320), (438, 2160), (441, 2160), (503, 2160), (727, 4320), (747, 2160), (869, 2160), (1224, 4320), (1231, 2160), (1276, 4320), (1280, 4320), (1316, 4320), (1471, 4320), (1473, 4320), (1476, 2160), (1620, 2160), (1622, 2160), (2097, 4320)]

def row1657 : Integer.Sparse (Fin 3237) := [(659, -1), (1176, -1), (1394, -2), (1468, -2), (1477, -1), (1577, -2), (1595, -1), (1608, -2), (1629, -1), (1631, -1), (1979, -1), (2538, -1), (2878, 8), (2880, 4), (2881, 4), (2886, 8), (2893, 4), (2922, 4), (2996, 8), (3002, 4), (3010, 8), (3015, 8), (3049, 8), (3137, 8), (3138, 4), (3195, 4)]

def row1658 : Integer.Sparse (Fin 3237) := [(1126, 2), (1127, 1), (1135, 1), (1152, 2), (1171, 1), (1174, 1), (1176, 1), (1556, 2), (1576, 2), (1577, 2), (1604, 2), (1607, 2), (1608, 2), (1627, 1), (1629, 1), (1631, 1), (1944, 2), (1965, 1), (1978, 1), (1979, 1)]

def row1659 : Integer.Sparse (Fin 3237) := [(593, 1), (1243, 1), (1354, 2), (1473, 1), (1477, 1), (2831, -1)]

def row1660 : Integer.Sparse (Fin 3237) := [(894, 1), (1348, 1), (1354, 1), (1394, 1), (1473, 1), (2096, 1), (2831, -1)]

def row1661 : Integer.Sparse (Fin 3237) := [(0, 19), (3, 20), (4, 5), (32, -30), (261, -50), (686, -2160), (1094, -2160), (1394, -4320), (1416, -4320), (1426, -4320), (1440, -4320), (1470, -2160), (1577, -4320), (1580, -4320), (1609, -2160), (1786, -2160), (2451, -2160), (2564, -2160), (2933, 17280), (2935, 8640), (2938, 8640), (3028, 17280), (3036, 17280), (3038, 17280), (3041, 17280), (3043, 8640), (3049, 17280), (3057, 8640), (3061, 8640), (3126, 17280)]

def row1662 : Integer.Sparse (Fin 3237) := [(0, -96), (3, -40), (4, -30), (32, 160), (160, 160), (162, 160), (165, 320), (261, 230), (1083, 8640), (1094, 4320), (1095, 4320), (1103, 4320), (1394, 8640), (1426, 4320), (1432, 8640), (1440, 8640), (1441, 8640), (1451, 8640), (1453, 8640), (1470, 4320), (1474, 4320), (1481, 8640), (1494, 4320), (1495, 4320), (1855, 8640)]

def row1663 : Integer.Sparse (Fin 3237) := [(763, 1), (1671, 1), (1720, 1), (1755, 1), (1822, 1), (1837, 1), (2840, -1)]

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

def row1664 : Integer.Sparse (Fin 3237) := [(880, 1), (1999, 1), (2020, 1), (2032, 2), (2050, 1), (2839, -1)]

def row1665 : Integer.Sparse (Fin 3237) := [(892, 1), (1983, 1), (1988, 1), (1999, 1), (2032, 1), (2087, 1), (2839, -1)]

def row1666 : Integer.Sparse (Fin 3237) := [(1387, 1), (1435, 1), (1442, 1), (1460, 1), (1561, 1), (2488, 1), (2829, -1)]

def row1667 : Integer.Sparse (Fin 3237) := [(1384, 1), (1387, 1), (1396, 1), (1416, 1), (1609, 1), (2488, 1), (2829, -1)]

def row1668 : Integer.Sparse (Fin 3237) := [(740, -1), (1655, -1), (1713, -1), (1753, -1), (1758, -1), (1761, -1), (1934, -1), (2081, -1), (2087, -1), (2097, -1), (2177, -1), (2283, -1), (2396, -1), (2425, -1), (2437, -1), (2449, -1), (2450, -1), (2501, -1), (2555, -1), (2556, -1), (2561, -1), (2573, -1), (2866, 4), (2868, 4), (2873, 4), (2876, 4), (2911, 4), (2942, 4), (2949, 4), (2961, 4), (3068, 8), (3072, 4), (3074, 4), (3095, 4), (3103, 4), (3122, 4), (3126, 4), (3171, 4)]

def row1669 : Integer.Sparse (Fin 3237) := [(0, -304), (3, -160), (4, 60), (32, 180), (160, 320), (165, 320), (261, -680), (549, 5760), (551, 5760), (556, 5760), (566, 5760), (636, 5760), (752, 5760), (758, 5760), (804, 5760), (1639, 5760), (1644, 5760), (1652, 5760), (1706, 5760), (1710, 5760), (1743, 5760), (1801, 5760), (1812, 5760), (1925, 5760)]

def row1670 : Integer.Sparse (Fin 3237) := [(1111, 1), (1112, 1), (1116, 1), (1129, 1), (1155, 1), (2270, 1), (2282, 1), (2283, 1), (2301, 1), (2385, 2), (2389, 1), (2395, 1), (2396, 1), (2421, 1), (2425, 1), (2436, 1), (2437, 1), (2449, 1), (2450, 1), (2479, 1), (2482, 1), (2500, 1), (2501, 1), (2555, 1), (2556, 1), (2561, 1), (2573, 1)]

def row1671 : Integer.Sparse (Fin 3237) := [(740, 1), (1655, 1), (1713, 1), (1758, 2), (2839, -1)]

def row1672 : Integer.Sparse (Fin 3237) := [(0, 111), (4, -5), (32, 20), (66, 80), (160, 160), (225, 160), (261, -310), (411, -4320), (414, -4320), (417, -4320), (423, -4320), (454, -4320), (456, -4320), (458, -4320), (460, -4320), (473, -4320), (514, -4320), (709, -4320), (713, -4320), (732, -4320), (825, -4320), (1184, -4320), (1189, -4320), (1195, -4320), (1256, -4320), (1258, -4320), (1260, -4320), (1261, -4320), (1266, -4320), (1269, -4320), (1285, -4320), (1287, -4320), (1288, -4320), (1294, -4320), (1325, -4320), (1340, -4320), (1345, -4320), (1392, -4320), (1394, -8640), (1397, -4320), (1424, -4320), (1426, -4320), (1541, -4320), (1543, -4320), (1545, -4320), (1567, -4320), (1568, -4320), (1569, -4320), (1577, -8640), (1579, -4320), (1580, -4320), (1593, -4320), (1595, -4320), (1618, -4320), (1631, -4320), (2081, -4320), (2087, -4320), (2555, -4320), (2561, -4320), (2562, -4320), (2578, -4320), (2765, -4320)]

def row1673 : Integer.Sparse (Fin 3237) := [(570, -1), (659, -1), (1130, -1), (1176, -1), (1224, -1), (1340, -1), (1389, -1), (1394, -2), (1398, -1), (1473, -1), (1524, -1), (1541, -1), (1560, -1), (1577, -2), (1578, -1), (1595, -1), (1628, -1), (1631, -1), (1948, -1), (2491, -1), (2866, 4), (2869, 4), (2871, 4), (2873, 4), (2874, 4), (2878, 4), (2913, 4), (2976, 4), (2982, 4), (3004, 4), (3010, 4), (3015, 4), (3020, 4), (3132, 4), (3133, 4), (3137, 4), (3184, 4)]

def row1674 : Integer.Sparse (Fin 3237) := [(0, -420), (3, -80), (4, 60), (32, -460), (68, 320), (160, 320), (162, 640), (165, 320), (261, -580), (552, 5760), (554, 5760), (557, 5760), (571, 5760), (638, 5760), (887, 5760), (891, 5760), (1641, 5760), (1645, 5760), (1656, 5760), (1707, 5760), (1714, 5760), (1744, 5760), (1824, 5760), (1825, 5760), (1841, 5760), (1959, 5760)]

def row1675 : Integer.Sparse (Fin 3237) := [(1111, 1), (1124, 1), (1125, 1), (1126, 1), (1128, 1), (1129, 1), (1130, 1), (1170, 1), (1176, 1), (1506, 1), (1523, 1), (1524, 1), (1540, 1), (1541, 1), (1556, 1), (1559, 1), (1560, 1), (1576, 1), (1577, 2), (1578, 1), (1628, 1), (1631, 1), (1904, 1), (1916, 1), (1944, 1), (1947, 1), (1948, 1)]

def row1676 : Integer.Sparse (Fin 3237) := [(556, 1), (1209, 1), (1334, 1), (1354, 1), (1394, 1), (1398, 1), (2831, -1)]

def row1677 : Integer.Sparse (Fin 3237) := [(886, 1), (1334, 1), (1340, 1), (1394, 2), (2080, 1), (2831, -1)]

def row1678 : Integer.Sparse (Fin 3237) := [(570, 1), (1224, 1), (1340, 1), (1394, 2), (2831, -1)]

def row1679 : Integer.Sparse (Fin 3237) := [(0, 19), (3, 20), (4, 5), (32, -30), (261, -50), (618, -2160), (1051, -2160), (1294, -2160), (1306, -2160), (1316, -2160), (1325, -2160), (1328, -2160), (1329, -2160), (1359, -2160), (1367, -2160), (1391, -2160), (1394, -4320), (1426, -2160), (1473, -2160), (1561, -2160), (1577, -4320), (1580, -2160), (1628, -2160), (1758, -4320), (2449, -4320), (2564, -2160), (2903, 8640), (2904, 8640), (2905, 8640), (2933, 8640), (3016, 8640), (3017, 8640), (3020, 8640), (3021, 8640), (3028, 17280), (3033, 8640), (3034, 8640), (3036, 8640), (3049, 8640), (3122, 8640)]

def row1680 : Integer.Sparse (Fin 3237) := [(1686, 1), (1689, 1), (1691, 1), (1698, 1), (1902, 1), (2669, 1), (2836, -1)]

def row1681 : Integer.Sparse (Fin 3237) := [(1294, 1), (1296, 1), (1549, 1), (2430, 1), (2827, -1)]

def row1682 : Integer.Sparse (Fin 3237) := [(1437, 1), (1441, 1), (1443, 1), (1463, 1), (1562, 1), (2520, 1), (2828, -1)]

def row1683 : Integer.Sparse (Fin 3237) := [(885, 1), (1995, 2), (2004, 1), (2052, 1), (2055, 1), (2840, -1)]

def row1684 : Integer.Sparse (Fin 3237) := [(749, -1), (1661, -1), (1718, -2), (1782, -2), (1950, -1), (2047, -2), (2055, -1), (2160, -1), (2287, -1), (2399, -1), (2427, -2), (2439, -2), (2503, -1), (2572, -2), (2574, -1), (2577, -1), (2886, 8), (2889, 4), (2893, 4), (2929, 4), (2954, 8), (2969, 4), (3074, 8), (3095, 8), (3114, 8), (3126, 8), (3182, 4)]

def row1685 : Integer.Sparse (Fin 3237) := [(1152, 2), (1154, 1), (1159, 1), (1174, 1), (2276, 2), (2287, 1), (2312, 1), (2389, 2), (2399, 1), (2421, 2), (2427, 2), (2439, 2), (2440, 2), (2482, 2), (2503, 1), (2504, 1), (2572, 2), (2574, 1), (2577, 1)]

def row1686 : Integer.Sparse (Fin 3237) := [(0, 17), (32, -10), (160, -80), (225, -40), (261, 5), (423, -2160), (426, -1080), (427, -1080), (460, -2160), (462, -1080), (463, -1080), (491, -1080), (517, -1080), (702, -2160), (707, -1080), (825, -1080), (1195, -2160), (1198, -1080), (1261, -2160), (1263, -1080), (1264, -1080), (1269, -2160), (1272, -2160), (1288, -2160), (1290, -2160), (1291, -2160), (1306, -2160), (1328, -2160), (1394, -2160), (1424, -2160), (1429, -1080), (1569, -2160), (1571, -1080), (1577, -2160), (1579, -1080), (1595, -1080), (1611, -1080), (1619, -1080), (1631, -1080), (2047, -2160), (2055, -1080), (2572, -2160), (2577, -1080), (2578, -1080), (2766, -1080)]

def row1687 : Integer.Sparse (Fin 3237) := [(579, -1), (697, -1), (1134, -1), (1179, -1), (1231, -1), (1345, -2), (1422, -2), (1426, -2), (1528, -1), (1545, -2), (1562, -2), (1580, -2), (1622, -1), (1632, -1), (1950, -1), (2503, -1), (2876, 8), (2880, 4), (2890, 8), (2894, 4), (2930, 4), (2987, 8), (3005, 8), (3033, 8), (3150, 8), (3151, 4), (3185, 4)]

def row1688 : Integer.Sparse (Fin 3237) := [(1116, 2), (1134, 1), (1135, 1), (1168, 2), (1169, 1), (1172, 1), (1179, 1), (1512, 2), (1528, 1), (1534, 2), (1545, 2), (1562, 2), (1563, 2), (1580, 2), (1632, 1), (1910, 1), (1921, 2), (1950, 1), (1951, 1)]

def row1689 : Integer.Sparse (Fin 3237) := [(579, 1), (1231, 1), (1345, 2), (1426, 1), (2832, -1)]

def row1690 : Integer.Sparse (Fin 3237) := [(875, 1), (1338, 1), (1345, 1), (1426, 2), (2045, 1), (2832, -1)]

def row1691 : Integer.Sparse (Fin 3237) := [(1488, 2), (1490, 1), (1496, 1), (1617, 1), (1910, 1), (2830, -1)]

def row1692 : Integer.Sparse (Fin 3237) := [(1446, 1), (1448, 1), (1454, 1), (1462, 1), (1590, 1), (2525, 1), (2828, -1)]

def row1693 : Integer.Sparse (Fin 3237) := [(1764, 1), (1843, 1), (1845, 1), (1865, 1), (1896, 1), (2701, 1), (2836, -1)]

def row1694 : Integer.Sparse (Fin 3237) := [(1399, 1), (1401, 1), (1407, 1), (1417, 1), (1617, 1), (2495, 1), (2830, -1)]

def row1695 : Integer.Sparse (Fin 3237) := [(1742, 1), (1846, 1), (1850, 2), (1913, 1), (2692, 1), (2838, -1)]

def row1696 : Integer.Sparse (Fin 3237) := [(1377, 1), (1380, 1), (1385, 2), (1590, 1), (2483, 1), (2828, -1)]

def row1697 : Integer.Sparse (Fin 3237) := [(1478, 1), (1480, 1), (1482, 1), (1488, 1), (1568, 1), (1904, 1), (2830, -1)]

def row1698 : Integer.Sparse (Fin 3237) := [(1431, 1), (1433, 1), (1436, 1), (1446, 1), (1548, 1), (2512, 1), (2828, -1)]

def row1699 : Integer.Sparse (Fin 3237) := [(1729, 1), (1731, 1), (1735, 1), (1762, 1), (1914, 1), (2689, 1), (2836, -1)]

def row1700 : Integer.Sparse (Fin 3237) := [(1729, 1), (1793, 1), (1796, 1), (1818, 1), (1896, 1), (2689, 1), (2836, -1)]

def row1701 : Integer.Sparse (Fin 3237) := [(1362, 1), (1364, 1), (1368, 1), (1399, 1), (1568, 1), (2476, 1), (2830, -1)]

def row1702 : Integer.Sparse (Fin 3237) := [(656, -1), (869, -1), (1157, -1), (1391, -2), (1467, -2), (1470, -2), (1476, -1), (1561, -2), (1590, -2), (1609, -2), (1617, -1), (1630, -1), (1969, -1), (1980, -2), (2537, -1), (2884, 8), (2889, 4), (2892, 4), (2956, 8), (2958, 4), (2994, 8), (3001, 4), (3009, 8), (3014, 8), (3135, 8), (3138, 4)]

def row1703 : Integer.Sparse (Fin 3237) := [(0, -57), (4, 5), (32, 80), (68, -80), (255, -80), (261, 60), (741, 1440), (746, 720), (750, 720), (880, 1440), (885, 720), (2000, 1440), (2005, 720), (2059, 1440), (2062, 1440), (2101, 1440), (2102, 720)]

def row1704 : Integer.Sparse (Fin 3237) := [(1140, 2), (1154, 1), (1157, 1), (1161, 1), (1547, 2), (1558, 2), (1561, 2), (1565, 2), (1587, 2), (1590, 2), (1606, 1), (1609, 2), (1614, 1), (1617, 1), (1630, 1), (1931, 2), (1965, 1), (1969, 1), (1980, 1)]

def row1705 : Integer.Sparse (Fin 3237) := [(592, 1), (1242, 1), (1353, 2), (1470, 1), (1476, 1), (2832, -1)]

def row1706 : Integer.Sparse (Fin 3237) := [(761, 1), (1347, 1), (1353, 1), (1391, 1), (1470, 1), (1835, 1), (2832, -1)]

def row1707 : Integer.Sparse (Fin 3237) := [(583, 1), (1235, 1), (1347, 1), (1467, 1), (1470, 2), (2832, -1)]

def row1708 : Integer.Sparse (Fin 3237) := [(0, 33), (3, -20), (32, 10), (66, -80), (160, -160), (256, -80), (261, 45), (431, -4320), (433, -2160), (440, -2160), (483, -4320), (485, -2160), (493, -2160), (501, -2160), (511, -2160), (559, -4320), (577, -2160), (651, -2160), (1077, -4320), (1091, -2160), (1123, -2160), (1219, -4320), (1230, -2160), (1274, -4320), (1279, -4320), (1300, -4320), (1308, -4320), (1314, -4320), (1323, -4320), (1416, -4320), (1429, -2160), (1440, -4320), (1468, -4320), (1477, -2160), (1510, -4320), (1527, -2160), (1571, -2160), (1608, -4320), (1611, -2160), (1619, -2160), (1629, -2160), (1837, -4320), (1969, -2160), (2519, -4320), (2537, -2160), (2563, -2160), (2769, -2160)]

def row1709 : Integer.Sparse (Fin 3237) := [(0, -33), (3, 20), (32, -10), (66, 80), (160, 160), (256, 80), (261, -45), (431, 4320), (433, 2160), (440, 2160), (501, 2160), (559, 4320), (577, 2160), (651, 2160), (1219, 4320), (1230, 2160), (1274, 4320), (1279, 4320), (1314, 4320), (1440, 4320), (1468, 4320), (1477, 2160), (1571, 2160), (1619, 2160), (1837, 4320), (1969, 2160)]

def row1710 : Integer.Sparse (Fin 3237) := [(735, -1), (828, -1), (1651, -1), (1709, -1), (1752, -1), (1755, -1), (1760, -1), (1808, -1), (1815, -1), (1837, -1), (1933, -1), (1936, -1), (2274, -1), (2310, -1), (2387, -1), (2419, -1), (2429, -1), (2438, -1), (2446, -1), (2475, -1), (2481, -1), (2490, -1), (2502, -1), (2519, -1), (2941, 4), (2942, 4), (2945, 4), (2948, 4), (2949, 4), (2954, 4), (2961, 4), (3071, 4), (3077, 4), (3085, 4), (3098, 4), (3131, 4)]

def row1711 : Integer.Sparse (Fin 3237) := [(2265, 1), (2270, 1), (2272, 1), (2274, 1), (2276, 1), (2278, 1), (2282, 1), (2301, 1), (2310, 1), (2387, 1), (2391, 1), (2419, 1), (2422, 1), (2428, 1), (2429, 1), (2438, 1), (2443, 1), (2446, 1), (2475, 1), (2481, 1), (2488, 1), (2490, 1), (2502, 1), (2519, 1)]

def row1712 : Integer.Sparse (Fin 3237) := [(723, 1), (1643, 1), (1663, 1), (1671, 1), (1755, 1), (1760, 1), (2840, -1)]

def row1713 : Integer.Sparse (Fin 3237) := [(715, 1), (1720, 1), (1752, 1), (1755, 2), (2840, -1)]

def row1714 : Integer.Sparse (Fin 3237) := [(735, 1), (1651, 1), (1709, 1), (1755, 1), (2840, -1)]

def row1715 : Integer.Sparse (Fin 3237) := [(0, 199), (3, 40), (4, 5), (71, 80), (261, 60), (523, -4320), (525, -4320), (531, -4320), (535, -4320), (545, -4320), (548, -4320), (565, -4320), (602, -4320), (656, -4320), (1020, -4320), (1022, -4320), (1025, -4320), (1033, -4320), (1041, -4320), (1044, -4320), (1065, -4320), (1114, -4320), (1157, -4320), (1633, -4320), (1634, -4320), (1635, -4320), (1637, -4320), (1651, -4320), (1676, -4320), (1683, -4320), (1709, -4320), (1727, -4320), (1753, -4320), (1755, -4320), (1761, -4320), (1782, -4320), (1810, -4320), (1815, -4320), (1934, -4320), (1936, -4320), (2324, -4320), (2325, -4320), (2326, -4320), (2328, -4320), (2343, -4320), (2378, -4320), (2387, -4320), (2405, -4320), (2419, -4320), (2437, -4320), (2438, -4320), (2439, -4320), (2450, -4320), (2480, -4320), (2481, -4320), (2501, -4320), (2502, -4320), (2557, -4320), (2558, -4320), (2575, -4320), (2803, -4320)]

def row1716 : Integer.Sparse (Fin 3237) := [(565, -1), (656, -1), (825, -1), (1114, -1), (1157, -1), (1219, -1), (1337, -1), (1388, -1), (1391, -2), (1397, -1), (1470, -1), (1510, -1), (1532, -1), (1548, -1), (1561, -2), (1568, -1), (1579, -1), (1609, -1), (1933, -1), (1949, -2), (2490, -1), (2868, 4), (2872, 4), (2946, 4), (2950, 4), (2956, 4), (2975, 4), (2981, 4), (3003, 4), (3009, 4), (3014, 4), (3127, 4), (3135, 4)]

def row1717 : Integer.Sparse (Fin 3237) := [(0, -106), (3, -20), (4, 20), (32, 130), (68, 80), (255, 80), (261, 140), (720, 1080), (722, 1080), (725, 1080), (741, 1080), (892, 1080), (1986, 1080), (1989, 1080), (2000, 1080), (2056, 1080), (2059, 1080), (2089, 1080), (2101, 1080)]

def row1718 : Integer.Sparse (Fin 3237) := [(1112, 1), (1114, 1), (1119, 1), (1157, 1), (1499, 1), (1508, 1), (1510, 1), (1514, 1), (1531, 1), (1532, 1), (1535, 1), (1547, 1), (1548, 1), (1558, 1), (1561, 2), (1565, 1), (1568, 1), (1579, 1), (1609, 1), (1894, 1), (1931, 1), (1933, 1), (1949, 1)]

def row1719 : Integer.Sparse (Fin 3237) := [(555, 1), (1208, 1), (1333, 1), (1353, 1), (1391, 1), (1397, 1), (2832, -1)]

def row1720 : Integer.Sparse (Fin 3237) := [(751, 1), (1333, 1), (1337, 1), (1391, 2), (2832, -1)]

def row1721 : Integer.Sparse (Fin 3237) := [(1202, 1), (1347, 1), (1388, 1), (1391, 2), (2832, -1)]

def row1722 : Integer.Sparse (Fin 3237) := [(565, 1), (1219, 1), (1337, 1), (1391, 1), (2832, -1)]

def row1723 : Integer.Sparse (Fin 3237) := [(0, 86), (4, -5), (32, 20), (66, 80), (160, 160), (256, 80), (261, 155), (408, -4320), (410, -4320), (416, -4320), (420, -4320), (444, -4320), (446, -4320), (449, -4320), (457, -4320), (471, -4320), (487, -4320), (543, -4320), (547, -4320), (562, -4320), (599, -4320), (1039, -4320), (1043, -4320), (1048, -4320), (1107, -4320), (1182, -4320), (1188, -4320), (1192, -4320), (1247, -4320), (1251, -4320), (1259, -4320), (1265, -4320), (1267, -4320), (1282, -4320), (1286, -4320), (1293, -4320), (1302, -4320), (1337, -4320), (1344, -4320), (1359, -4320), (1367, -4320), (1373, -4320), (1376, -4320), (1389, -4320), (1391, -4320), (1398, -4320), (1421, -4320), (1422, -4320), (1532, -4320), (1544, -4320), (1551, -4320), (1560, -4320), (1561, -4320), (1562, -4320), (1578, -4320), (1592, -4320), (1610, -4320), (1808, -4320), (1815, -4320), (1933, -4320), (2475, -4320), (2481, -4320), (2490, -4320), (2554, -4320), (2764, -4320)]

def row1724 : Integer.Sparse (Fin 3237) := [(1687, 1), (1795, 1), (1799, 1), (1833, 1), (1909, 1), (2668, 1), (2837, -1)]

def row1725 : Integer.Sparse (Fin 3237) := [(1311, 1), (1314, 1), (1318, 1), (1568, 1), (2446, 1), (2830, -1)]

def row1726 : Integer.Sparse (Fin 3237) := [(1314, 1), (1794, 1), (1798, 1), (1832, 1), (1908, 1), (2446, 1), (2830, -1)]

def row1727 : Integer.Sparse (Fin 3237) := [(1679, 1), (1680, 2), (1888, 1), (2657, 1), (2836, -1)]

def row1728 : Integer.Sparse (Fin 3237) := [(1800, 1), (1807, 2), (1920, 1), (2657, 1), (2836, -1)]

def row1729 : Integer.Sparse (Fin 3237) := [(1293, 1), (1806, 2), (1919, 1), (2429, 1), (2828, -1)]

def row1730 : Integer.Sparse (Fin 3237) := [(1436, 1), (1440, 1), (1443, 1), (1462, 1), (2519, 1), (2828, -1)]

def row1731 : Integer.Sparse (Fin 3237) := [(727, 1), (1274, 1), (1279, 1), (1440, 1), (1776, 1), (2828, -1)]

def row1732 : Integer.Sparse (Fin 3237) := [(559, 1), (1212, 1), (1273, 1), (1387, 1), (1416, 1), (2829, -1)]

def row1733 : Integer.Sparse (Fin 3237) := [(1727, 1), (1728, 1), (1750, 1), (1913, 1), (2838, -1)]

def row1734 : Integer.Sparse (Fin 3237) := [(565, -2), (574, -1), (578, -1), (732, -2), (747, -1), (825, -1), (1114, -2), (1132, -1), (1133, -1), (1219, -2), (1230, -1), (1337, -2), (1344, -2), (1391, -2), (1510, -2), (1526, -1), (1527, -1), (1532, -2), (1543, -2), (1544, -2), (1561, -2), (1579, -1), (1781, -2), (1789, -1), (1908, -1), (1919, -2), (1949, -2), (2832, 4)]

def row1735 : Integer.Sparse (Fin 3237) := [(1114, 2), (1132, 1), (1133, 1), (1510, 2), (1526, 1), (1527, 1), (1532, 2), (1543, 2), (1544, 2), (1561, 2), (1579, 1), (1908, 1), (1919, 2), (1949, 1), (2832, 1)]

def row1736 : Integer.Sparse (Fin 3237) := [(1680, 1), (1683, 1), (1684, 1), (1896, 1), (2836, -1)]

def row1737 : Integer.Sparse (Fin 3237) := [(1683, 1), (1735, 1), (1777, 1), (1920, 1), (2836, -1)]

def row1738 : Integer.Sparse (Fin 3237) := [(523, -1), (529, -1), (531, -1), (602, -1), (709, -1), (713, -1), (727, -1), (792, -1), (1020, -1), (1032, -1), (1033, -1), (1065, -1), (1182, -1), (1188, -1), (1247, -1), (1258, -1), (1259, -1), (1265, -1), (1274, -1), (1279, -1), (1285, -1), (1286, -1), (1293, -1), (1300, -1), (1302, -1), (1322, -1), (1323, -1), (1327, -1), (1359, -1), (1367, -1), (1416, -1), (1421, -1), (1440, -1), (1551, -1), (1695, -1), (1734, -2), (1741, -1), (1776, -2), (1781, -1), (1919, -1), (2828, 4)]

def row1739 : Integer.Sparse (Fin 3237) := [(536, -2), (542, -1), (628, -1), (1024, -2), (1037, -1), (1072, -1), (1193, -2), (1198, -1), (1250, -2), (1263, -1), (1268, -2), (1272, -2), (1281, -2), (1290, -2), (1306, -2), (1328, -2), (1331, -2), (1373, -2), (1376, -2), (1426, -1), (1580, -1), (1683, -2), (1700, -1), (1786, -1), (2343, -2), (2348, -1), (2451, -1), (2829, 4)]

def row1740 : Integer.Sparse (Fin 3237) := [(562, -4), (568, -1), (577, -2), (1107, -4), (1117, -1), (1123, -2), (1216, -4), (1229, -1), (1336, -2), (1421, -4), (1429, -2), (1502, -4), (1518, -1), (1529, -2), (1551, -4), (1571, -2), (1936, -1), (2502, -1), (2833, 4)]

def row1741 : Integer.Sparse (Fin 3237) := [(1107, 4), (1117, 1), (1123, 2), (1502, 4), (1518, 1), (1529, 2), (1551, 4), (1571, 2), (1936, 1), (2833, 1)]

def row1742 : Integer.Sparse (Fin 3237) := [(577, 1), (1216, 2), (1229, 1), (1429, 1), (2833, -1)]

def row1743 : Integer.Sparse (Fin 3237) := [(522, -1), (525, -1), (530, -1), (543, -1), (547, -1), (559, -1), (599, -1), (1018, -1), (1022, -1), (1027, -1), (1039, -1), (1043, -1), (1048, -1), (1077, -1), (1181, -1), (1187, -1), (1199, -1), (1212, -1), (1245, -1), (1253, -1), (1273, -1), (1283, -1), (1292, -1), (1293, -1), (1302, -1), (1308, -1), (1310, -1), (1314, -1), (1358, -2), (1359, -1), (1367, -1), (1373, -1), (1376, -1), (1387, -2), (1391, -1), (1416, -1), (1440, -1), (1561, -1), (1755, -1), (2438, -1), (2829, 4)]

def row1744 : Integer.Sparse (Fin 3237) := [(2812, 4), (2814, 1), (2815, 2), (2818, 2), (2822, 4), (2824, 1), (2825, 2), (2828, 4), (2829, 4), (2830, 2), (2832, 2), (2833, 1), (2840, 1)]

def row1745 : Integer.Sparse (Fin 3237) := [(1656, 1), (2000, 1), (2218, 1), (2226, 1), (2236, 1), (2622, 1), (2840, -1)]

def row1746 : Integer.Sparse (Fin 3237) := [(1566, 1), (1568, 1), (1570, 1), (1578, 1), (1615, 1), (2561, 1), (2830, -1)]

def row1747 : Integer.Sparse (Fin 3237) := [(553, 1), (1207, 1), (1352, 1), (1381, 1), (1389, 1), (1392, 1), (2831, -1)]

def row1748 : Integer.Sparse (Fin 3237) := [(1641, 1), (1986, 1), (2231, 1), (2237, 2), (2609, 1), (2839, -1)]

def row1749 : Integer.Sparse (Fin 3237) := [(1566, 1), (1692, 1), (2444, 1), (2559, 1), (2561, 2), (2830, -1)]

def row1750 : Integer.Sparse (Fin 3237) := [(2232, 1), (2582, 1), (2583, 1), (2585, 1), (2662, 2), (2836, -1)]

def row1751 : Integer.Sparse (Fin 3237) := [(590, 1), (1241, 1), (1352, 1), (1455, 1), (1468, 1), (1471, 1), (2831, -1)]

def row1752 : Integer.Sparse (Fin 3237) := [(1645, 1), (1989, 1), (2197, 1), (2202, 1), (2226, 1), (2610, 1), (2840, -1)]

def row1753 : Integer.Sparse (Fin 3237) := [(1615, 1), (1697, 1), (2493, 1), (2561, 1), (2576, 1), (2577, 1), (2830, -1)]

def row1754 : Integer.Sparse (Fin 3237) := [(1615, 2), (1617, 1), (1621, 1), (1629, 1), (2577, 1), (2830, -1)]

def row1755 : Integer.Sparse (Fin 3237) := [(2222, 1), (2584, 1), (2586, 1), (2587, 1), (2670, 2), (2837, -1)]

def row1756 : Integer.Sparse (Fin 3237) := [(1662, 1), (2005, 1), (2193, 2), (2217, 1), (2376, 1), (2832, -1)]

def row1757 : Integer.Sparse (Fin 3237) := [(2204, 1), (2352, 1), (2441, 1), (2448, 2), (2560, 1), (2830, -1)]

def row1758 : Integer.Sparse (Fin 3237) := [(745, 1), (1659, 1), (1717, 1), (1771, 1), (1782, 1), (1784, 1), (2840, -1)]

def row1759 : Integer.Sparse (Fin 3237) := [(1652, 1), (1995, 1), (2019, 1), (2055, 1), (2112, 1), (2621, 1), (2840, -1)]

def row1760 : Integer.Sparse (Fin 3237) := [(2444, 1), (2446, 1), (2448, 1), (2450, 1), (2481, 1), (2561, 1), (2830, -1)]

def row1761 : Integer.Sparse (Fin 3237) := [(1318, 1), (1898, 1), (2339, 1), (2403, 1), (2446, 1), (2448, 1), (2830, -1)]

def row1762 : Integer.Sparse (Fin 3237) := [(721, 1), (1642, 1), (1724, 1), (1746, 1), (1753, 1), (1756, 1), (2839, -1)]

def row1763 : Integer.Sparse (Fin 3237) := [(1639, 1), (1983, 1), (2063, 1), (2087, 1), (2114, 1), (2607, 1), (2839, -1)]

def row1764 : Integer.Sparse (Fin 3237) := [(1326, 1), (2444, 2), (2450, 2), (2830, -1)]

def row1765 : Integer.Sparse (Fin 3237) := [(1311, 1), (1892, 1), (2336, 1), (2444, 1), (2446, 2), (2830, -1)]

def row1766 : Integer.Sparse (Fin 3237) := [(1219, 1), (1711, 1), (1719, 1), (1789, 1), (1814, 1), (2370, 1), (2832, -1)]

def row1767 : Integer.Sparse (Fin 3237) := [(897, 1), (2010, 1), (2064, 1), (2089, 1), (2097, 1), (2101, 1), (2839, -1)]

def row1768 : Integer.Sparse (Fin 3237) := [(1832, 1), (1892, 1), (1894, 1), (1898, 1), (1904, 1), (2446, 1), (2830, -1)]

def row1769 : Integer.Sparse (Fin 3237) := [(1894, 1), (2446, 1), (2476, 1), (2481, 1), (2495, 1), (2563, 1), (2830, -1)]

def row1770 : Integer.Sparse (Fin 3237) := [(1663, 1), (1707, 1), (1715, 1), (1760, 1), (1803, 1), (2633, 1), (2840, -1)]

def row1771 : Integer.Sparse (Fin 3237) := [(755, 1), (1666, 1), (1715, 1), (1803, 1), (1808, 1), (1811, 1), (2840, -1)]

def row1772 : Integer.Sparse (Fin 3237) := [(889, 1), (2007, 1), (2060, 1), (2074, 1), (2081, 1), (2084, 1), (2839, -1)]

def row1773 : Integer.Sparse (Fin 3237) := [(1665, 1), (2056, 1), (2060, 1), (2074, 2), (2635, 1), (2839, -1)]

def row1774 : Integer.Sparse (Fin 3237) := [(1794, 1), (2403, 1), (2406, 1), (2446, 1), (2476, 2), (2830, -1)]

def row1775 : Integer.Sparse (Fin 3237) := [(1706, 2), (1716, 1), (1761, 1), (2674, 1), (2839, -1)]

def row1776 : Integer.Sparse (Fin 3237) := [(756, 1), (1667, 1), (1716, 1), (1810, 2), (2839, -1)]

def row1777 : Integer.Sparse (Fin 3237) := [(1368, 2), (1372, 1), (1413, 1), (1578, 1), (2830, -1)]

def row1778 : Integer.Sparse (Fin 3237) := [(2450, 1), (2481, 2), (2499, 1), (2565, 1), (2830, -1)]

def row1779 : Integer.Sparse (Fin 3237) := [(2065, 1), (2599, 1), (2601, 1), (2613, 1), (2690, 1), (2739, 1), (2838, -1)]

def row1780 : Integer.Sparse (Fin 3237) := [(0, 57), (3, 20), (32, -5), (66, 80), (160, 80), (261, 290), (742, -1440), (747, -720), (749, -720), (1224, -1440), (1231, -720), (1473, -720), (1524, -1440), (1526, -720), (1528, -720), (1628, -720), (1999, -1440), (2001, -1440), (2004, -720), (2060, -1440), (2097, -1440), (2280, -1440), (2287, -720), (2321, -720), (2543, -1440), (2546, -1440), (2549, -720), (2550, -1440), (2554, -1440), (2556, -1440), (2558, -720), (2563, -1440), (2579, -720), (2752, -1440), (2754, -720), (2766, -720)]

def row1781 : Integer.Sparse (Fin 3237) := [(0, -57), (3, -20), (32, 5), (66, -80), (160, -80), (261, -290), (742, 1440), (747, 720), (749, 720), (1224, 1440), (1231, 720), (1473, 720), (1999, 1440), (2001, 1440), (2004, 720), (2060, 1440), (2097, 1440)]

def row1782 : Integer.Sparse (Fin 3237) := [(0, 15), (3, 4), (32, -1), (66, 16), (160, 16), (261, -32), (572, -432), (577, -216), (579, -216), (662, -216), (1121, -432), (1123, -216), (1134, -216), (1164, -216), (1219, -432), (1230, -216), (1470, -216), (1510, -432), (1527, -216), (1609, -216), (1657, -432), (1661, -216), (1715, -432), (1718, -432), (1760, -432), (1837, -432), (1969, -216), (2393, -432), (2399, -216), (2423, -432), (2427, -432), (2446, -432), (2519, -432), (2537, -216), (2562, -432), (2564, -216), (2578, -216), (2753, -432), (2755, -216), (2769, -216)]

def row1783 : Integer.Sparse (Fin 3237) := [(0, -15), (3, -4), (32, 1), (66, -16), (160, -16), (261, 32), (572, 432), (577, 216), (579, 216), (662, 216), (1219, 432), (1230, 216), (1470, 216), (1657, 432), (1661, 216), (1715, 432), (1718, 432), (1760, 432), (1837, 432), (1969, 216)]

def row1784 : Integer.Sparse (Fin 3237) := [(0, 39), (3, -40), (32, 5), (66, -80), (71, -80), (160, -80), (261, 50), (1397, -4320), (1429, -2160), (1476, -2160), (1568, -4320), (1571, -2160), (1617, -2160), (1760, -8640), (1789, -4320), (1815, -4320), (1908, -4320), (2055, -2160), (2087, -4320), (2446, -8640), (2481, -4320), (2561, -4320), (2563, -2160), (2565, -2160), (2577, -2160), (3123, 17280), (3127, 17280), (3133, 17280), (3138, 8640), (3144, 17280), (3151, 8640)]

def row1785 : Integer.Sparse (Fin 3237) := [(0, -57), (3, 100), (32, -55), (66, -80), (160, -80), (261, 10), (1760, 1440), (1789, 720), (2033, 1440), (2054, 720), (2055, 720), (2074, 1440), (2086, 1440), (2087, 1440), (2089, 1440), (2102, 720)]

def row1786 : Integer.Sparse (Fin 3237) := [(0, 33), (3, 10), (71, 40), (261, -35), (743, -540), (748, -540), (1655, -1080), (1661, -540), (2002, -540), (2284, -540), (2286, -540), (2322, -270), (2396, -1080), (2399, -540), (2547, -540), (2557, -1080), (2564, -540), (2565, -540), (2755, -270), (2759, -540)]

def row1787 : Integer.Sparse (Fin 3237) := [(0, -33), (3, -10), (71, -40), (261, 35), (743, 540), (748, 540), (1655, 1080), (1661, 540), (2002, 540)]

def row1788 : Integer.Sparse (Fin 3237) := [(0, 9), (3, 2), (71, 8), (261, 5), (573, -144), (578, -144), (663, -72), (1131, -144), (1133, -144), (1177, -72), (1651, -288), (1658, -144), (1660, -144), (1716, -144), (1761, -144), (2387, -288), (2397, -144), (2398, -144), (2426, -144), (2450, -144), (2557, -288), (2558, -144), (2575, -144), (2799, -144), (2800, -72)]

def row1789 : Integer.Sparse (Fin 3237) := [(0, -9), (3, -2), (71, -8), (261, -5), (573, 144), (578, 144), (663, 72), (1651, 288), (1658, 144), (1660, 144), (1716, 144), (1761, 144)]

def row1790 : Integer.Sparse (Fin 3237) := [(0, 27), (3, -30), (32, 5), (66, -80), (71, -40), (160, -80), (261, 60), (1398, -2160), (1477, -1080), (1578, -2160), (1629, -1080), (1761, -4320), (1815, -4320), (2055, -2160), (2087, -4320), (2450, -4320), (2481, -4320), (2561, -4320), (2563, -2160), (2565, -1080), (2577, -2160), (3145, 8640)]

def row1791 : Integer.Sparse (Fin 3237) := [(2450, 2), (2565, 2), (2830, -1)]

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

def row1792 : Integer.Sparse (Fin 3237) := [(766, 1), (1674, 1), (1792, 1), (1825, 1), (1837, 1), (1841, 1), (2840, -1)]

def row1793 : Integer.Sparse (Fin 3237) := [(1224, 1), (2057, 1), (2062, 1), (2086, 2), (2373, 1), (2831, -1)]

def row1794 : Integer.Sparse (Fin 3237) := [(1692, 1), (1695, 1), (1697, 1), (1699, 1), (1904, 1), (2561, 1), (2830, -1)]

def row1795 : Integer.Sparse (Fin 3237) := [(1655, -1), (1758, -1), (1999, -1), (2058, -1), (2081, -1), (2087, -1), (2097, -1), (2177, -1), (2396, -1), (2449, -1), (2543, -1), (2551, -1), (2555, -1), (2556, -1), (2561, -1), (2573, -1), (2607, -1), (2611, -1), (2664, -1), (2671, -1), (2783, -1), (2786, -1), (2870, 4), (2872, 4), (2873, 4), (2879, 4), (2915, 4), (3068, 4), (3070, 4), (3071, 4), (3072, 4), (3076, 4), (3077, 4), (3097, 4), (3105, 4), (3129, 4), (3131, 4), (3136, 4), (3190, 4)]

def row1796 : Integer.Sparse (Fin 3237) := [(0, -308), (3, -240), (32, 400), (66, 320), (71, 320), (159, -960), (160, 320), (261, -620), (553, 5760), (555, 5760), (556, 5760), (575, 5760), (640, 5760), (1642, 5760), (1643, 5760), (1644, 5760), (1659, 5760), (1663, 5760), (1706, 5760), (1717, 5760), (1746, 5760), (1820, 5760), (1822, 5760), (1838, 5760), (1958, 5760)]

def row1797 : Integer.Sparse (Fin 3237) := [(1118, 1), (1119, 1), (1122, 1), (1129, 1), (1162, 1), (2385, 1), (2390, 1), (2391, 1), (2394, 1), (2395, 1), (2396, 1), (2422, 1), (2424, 1), (2444, 1), (2449, 1), (2488, 1), (2517, 1), (2520, 1), (2535, 1), (2543, 1), (2551, 1), (2555, 1), (2556, 1), (2561, 1), (2573, 1), (2664, 1), (2671, 1), (2786, 1)]

def row1798 : Integer.Sparse (Fin 3237) := [(1644, 1), (1988, 1), (2006, 1), (2009, 1), (2087, 1), (2611, 1), (2839, -1)]

def row1799 : Integer.Sparse (Fin 3237) := [(888, 1), (2006, 1), (2058, 1), (2081, 1), (2082, 1), (2087, 1), (2839, -1)]

def row1800 : Integer.Sparse (Fin 3237) := [(896, 1), (2009, 1), (2063, 1), (2087, 1), (2097, 1), (2098, 1), (2839, -1)]

def row1801 : Integer.Sparse (Fin 3237) := [(1695, 1), (2406, 1), (2481, 1), (2561, 1), (2830, -1)]

def row1802 : Integer.Sparse (Fin 3237) := [(2070, 1), (2337, 1), (2340, 1), (2346, 1), (2447, 1), (2525, 1), (2828, -1)]

def row1803 : Integer.Sparse (Fin 3237) := [(1671, 1), (1722, 1), (1726, 1), (1760, 1), (1857, 1), (2643, 1), (2840, -1)]

def row1804 : Integer.Sparse (Fin 3237) := [(1668, 1), (1984, 1), (1989, 1), (2001, 1), (2033, 1), (2610, 1), (2840, -1)]

def row1805 : Integer.Sparse (Fin 3237) := [(881, 1), (2001, 1), (2021, 1), (2033, 1), (2047, 1), (2051, 1), (2840, -1)]

def row1806 : Integer.Sparse (Fin 3237) := [(1798, 1), (2336, 1), (2339, 1), (2344, 1), (2446, 1), (2495, 1), (2830, -1)]

def row1807 : Integer.Sparse (Fin 3237) := [(1417, 1), (2365, 1), (2455, 1), (2481, 1), (2495, 1), (2499, 1), (2830, -1)]

def row1808 : Integer.Sparse (Fin 3237) := [(1985, 1), (1988, 2), (2002, 1), (2034, 1), (2611, 1), (2839, -1)]

def row1809 : Integer.Sparse (Fin 3237) := [(882, 1), (2002, 1), (2022, 1), (2034, 1), (2050, 2), (2839, -1)]

def row1810 : Integer.Sparse (Fin 3237) := [(1231, 1), (1996, 2), (2005, 1), (2054, 1), (2376, 1), (2832, -1)]

def row1811 : Integer.Sparse (Fin 3237) := [(1661, -1), (1786, -1), (1997, -2), (2004, -1), (2047, -2), (2160, -1), (2399, -1), (2451, -1), (2548, -2), (2549, -1), (2572, -2), (2574, -1), (2621, -2), (2665, -2), (2787, -2), (2891, 8), (2892, 4), (2893, 4), (2931, 4), (3074, 8), (3085, 8), (3101, 8), (3115, 8), (3148, 8), (3149, 4), (3198, 4)]

def row1812 : Integer.Sparse (Fin 3237) := [(1160, 2), (1161, 1), (1166, 1), (1174, 1), (2389, 2), (2399, 1), (2442, 2), (2443, 2), (2448, 2), (2451, 1), (2533, 2), (2534, 1), (2539, 1), (2548, 2), (2549, 1), (2572, 2), (2574, 1), (2665, 2), (2787, 1)]

def row1813 : Integer.Sparse (Fin 3237) := [(1661, 1), (1997, 2), (2004, 1), (2055, 1), (2840, -1)]

def row1814 : Integer.Sparse (Fin 3237) := [(1793, 1), (2598, 1), (2600, 1), (2612, 1), (2689, 1), (2711, 1), (2836, -1)]

def row1815 : Integer.Sparse (Fin 3237) := [(832, -1), (1651, -1), (1712, -1), (1718, -1), (1755, -1), (1808, -1), (1815, -1), (1837, -1), (1950, -1), (2311, -1), (2387, -1), (2420, -1), (2427, -1), (2438, -1), (2475, -1), (2481, -1), (2503, -1), (2519, -1), (2606, -1), (2610, -1), (2657, -1), (2668, -1), (2723, -2), (2947, 4), (2948, 4), (2949, 4), (2957, 4), (3071, 4), (3078, 4), (3079, 4), (3082, 4), (3086, 4), (3120, 4), (3126, 4), (3136, 4)]

def row1816 : Integer.Sparse (Fin 3237) := [(0, -99), (3, -80), (32, -5), (66, 80), (71, 80), (160, 80), (261, 130), (721, 1080), (723, 1080), (724, 1080), (745, 1080), (1665, 1080), (1668, 1080), (1855, 1080), (1987, 1080), (1988, 1080), (2003, 1080), (2061, 1080), (2098, 1080)]

def row1817 : Integer.Sparse (Fin 3237) := [(2277, 1), (2278, 1), (2281, 1), (2282, 1), (2311, 1), (2387, 1), (2391, 1), (2420, 1), (2427, 1), (2438, 1), (2470, 1), (2472, 1), (2474, 1), (2475, 1), (2481, 1), (2482, 1), (2503, 1), (2510, 1), (2511, 1), (2519, 1), (2520, 1), (2657, 1), (2668, 1), (2723, 1)]

def row1818 : Integer.Sparse (Fin 3237) := [(1643, 1), (1664, 1), (1668, 1), (1672, 1), (1815, 1), (2610, 1), (2840, -1)]

def row1819 : Integer.Sparse (Fin 3237) := [(753, 1), (1664, 1), (1712, 1), (1808, 1), (1815, 1), (2840, -1)]

def row1820 : Integer.Sparse (Fin 3237) := [(1790, 1), (1791, 1), (1815, 2), (2606, 1), (2840, -1)]

def row1821 : Integer.Sparse (Fin 3237) := [(764, 1), (1672, 1), (1791, 1), (1815, 1), (1837, 1), (1838, 1), (2840, -1)]

def row1822 : Integer.Sparse (Fin 3237) := [(0, 199), (4, -10), (32, 80), (66, 80), (71, 80), (160, 160), (256, 80), (261, 75), (546, -4320), (547, -4320), (548, -4320), (567, -4320), (605, -4320), (1042, -4320), (1043, -4320), (1044, -4320), (1066, -4320), (1115, -4320), (1182, -4320), (1188, -4320), (1192, -4320), (1247, -4320), (1251, -4320), (1259, -4320), (1391, -4320), (1561, -4320), (1633, -4320), (1634, -4320), (1635, -4320), (1638, -4320), (1653, -4320), (1677, -4320), (1684, -4320), (1712, -4320), (1728, -4320), (1755, -4320), (1808, -4320), (1810, -4320), (1933, -4320), (1934, -4320), (2324, -4320), (2325, -4320), (2326, -4320), (2329, -4320), (2344, -4320), (2379, -4320), (2388, -4320), (2406, -4320), (2420, -4320), (2438, -4320), (2475, -4320), (2480, -4320), (2490, -4320), (2501, -4320), (2554, -4320), (2557, -4320), (2607, -4320), (2611, -4320), (2621, -4320), (2664, -4320), (2665, -4320), (2671, -4320), (2764, -4320), (2803, -4320)]

def row1823 : Integer.Sparse (Fin 3237) := [(1800, 1), (2581, 1), (2657, 2), (2836, -1)]

def row1824 : Integer.Sparse (Fin 3237) := [(1732, 1), (1960, 1), (2599, 1), (2672, 1), (2690, 2), (2838, -1)]

def row1825 : Integer.Sparse (Fin 3237) := [(742, -1), (1657, -1), (1715, -1), (1752, -1), (1755, -1), (1784, -1), (1933, -1), (2280, -1), (2393, -1), (2423, -1), (2429, -1), (2438, -1), (2447, -1), (2490, -1), (2610, -1), (2633, -1), (2643, -1), (2668, -1), (2689, -1), (2699, -1), (2701, -1), (2703, -1), (2943, 4), (2948, 4), (2950, 4), (2962, 4), (2976, 4), (2982, 4), (2987, 4), (3049, 4), (3069, 4), (3071, 4), (3077, 4), (3085, 4), (3099, 4), (3108, 4), (3123, 4), (3144, 4), (3175, 4)]

def row1826 : Integer.Sparse (Fin 3237) := [(1506, 1), (1508, 1), (1512, 1), (1523, 1), (1607, 1), (2268, 1), (2278, 1), (2280, 1), (2305, 1), (2383, 1), (2391, 1), (2393, 1), (2422, 1), (2423, 1), (2429, 1), (2432, 1), (2433, 1), (2438, 1), (2443, 1), (2447, 1), (2476, 1), (2490, 1), (2495, 1), (2497, 1), (2668, 1), (2689, 1), (2701, 1), (2703, 1)]

def row1827 : Integer.Sparse (Fin 3237) := [(1640, 1), (1643, 1), (1645, 1), (1657, 1), (1760, 1), (2610, 1), (2840, -1)]

def row1828 : Integer.Sparse (Fin 3237) := [(743, -1), (1658, -1), (1716, -1), (1753, -2), (1758, -2), (1934, -2), (2284, -1), (2397, -1), (2426, -1), (2437, -2), (2449, -2), (2501, -2), (2611, -1), (2671, -1), (2674, -1), (2685, -1), (2691, -1), (2705, -1), (2944, 4), (2949, 8), (2963, 4), (3068, 8), (3072, 8), (3074, 8), (3100, 4), (3145, 4)]

def row1829 : Integer.Sparse (Fin 3237) := [(2271, 1), (2282, 2), (2284, 1), (2307, 1), (2385, 2), (2389, 2), (2395, 2), (2397, 1), (2426, 1), (2435, 1), (2437, 2), (2449, 2), (2499, 1), (2501, 2), (2671, 1), (2691, 1), (2705, 1)]

def row1830 : Integer.Sparse (Fin 3237) := [(1644, 2), (1658, 1), (1761, 1), (2611, 1), (2839, -1)]

def row1831 : Integer.Sparse (Fin 3237) := [(747, -1), (1219, -2), (1230, -1), (1510, -2), (1526, -1), (1527, -1), (1781, -2), (1896, -2), (1909, -1), (1919, -2), (1949, -2), (2160, -1), (2370, -2), (2376, -1), (2574, -1), (2955, 8), (2958, 4), (2970, 4), (2996, 8), (3002, 4), (3061, 4), (3075, 8), (3096, 8), (3119, 8), (3127, 8), (3185, 4)]

def row1832 : Integer.Sparse (Fin 3237) := [(1510, 2), (1526, 1), (1527, 1), (1604, 2), (1606, 1), (1612, 1), (1627, 1), (1880, 2), (1885, 2), (1886, 2), (1894, 2), (1896, 2), (1906, 1), (1909, 1), (1919, 2), (1949, 1), (2134, 2), (2158, 1), (2160, 1)]

def row1833 : Integer.Sparse (Fin 3237) := [(738, -2), (748, -1), (749, -1), (832, -1), (1651, -2), (1653, -2), (1660, -1), (1661, -1), (1712, -2), (1718, -2), (1782, -2), (1786, -1), (1815, -2), (1950, -1), (2275, -2), (2286, -1), (2287, -1), (2311, -1), (2387, -2), (2388, -2), (2398, -1), (2399, -1), (2420, -2), (2427, -2), (2439, -2), (2451, -1), (2481, -2), (2503, -1), (2840, 4)]

def row1834 : Integer.Sparse (Fin 3237) := [(2275, 2), (2286, 1), (2287, 1), (2311, 1), (2387, 2), (2388, 2), (2398, 1), (2399, 1), (2420, 2), (2427, 2), (2439, 2), (2451, 1), (2481, 2), (2503, 1), (2840, 1)]

def row1835 : Integer.Sparse (Fin 3237) := [(710, -1), (714, -2), (728, -1), (795, -1), (1633, -2), (1634, -2), (1636, -1), (1647, -1), (1683, -2), (1708, -1), (1735, -2), (1777, -2), (1800, -1), (1920, -2), (2259, -1), (2262, -2), (2264, -1), (2294, -1), (2324, -2), (2326, -2), (2343, -2), (2377, -1), (2381, -1), (2402, -2), (2410, -1), (2418, -2), (2452, -1), (2460, -2), (2836, 4)]

def row1836 : Integer.Sparse (Fin 3237) := [(1679, 1), (2581, 1), (2632, 2), (2657, 1), (2659, 1), (2836, -1)]

def row1837 : Integer.Sparse (Fin 3237) := [(1684, 1), (2600, 1), (2619, 1), (2665, 1), (2836, -1)]

def row1838 : Integer.Sparse (Fin 3237) := [(703, -2), (708, -2), (783, -1), (1635, -4), (1675, -2), (1696, -4), (1700, -2), (1799, -2), (1909, -2), (2243, -2), (2247, -2), (2258, -1), (2325, -4), (2327, -2), (2335, -4), (2348, -2), (2352, -2), (2376, -2), (2837, 4)]

def row1839 : Integer.Sparse (Fin 3237) := [(662, -1), (1164, -1), (1397, -2), (1467, -2), (1470, -1), (1568, -2), (1590, -2), (1609, -1), (1611, -1), (1619, -1), (1969, -1), (2537, -1), (2887, 8), (2892, 4), (2894, 4), (2989, 8), (2991, 4), (2997, 8), (3001, 4), (3011, 8), (3014, 8), (3055, 8), (3057, 4), (3178, 8), (3196, 4), (3198, 4)]

def row1840 : Integer.Sparse (Fin 3237) := [(0, -120), (3, -40), (32, 170), (219, 480), (261, 290), (881, 4320), (883, 2160), (885, 2160), (1225, 4320), (1232, 2160), (1474, 2160), (2000, 4320), (2005, 2160), (2148, 4320), (2161, 2160), (2162, 2160), (2195, 4320), (2219, 4320), (2230, 4320)]

def row1841 : Integer.Sparse (Fin 3237) := [(1147, 2), (1161, 1), (1164, 1), (1169, 1), (1521, 2), (1522, 1), (1552, 2), (1565, 2), (1568, 2), (1590, 2), (1597, 2), (1599, 2), (1609, 1), (1614, 1), (1619, 1), (1623, 1), (1939, 2), (1969, 1), (1971, 1), (1974, 1)]

def row1842 : Integer.Sparse (Fin 3237) := [(1238, 2), (1242, 1), (1244, 1), (1476, 1), (2162, 1), (2832, -1)]

def row1843 : Integer.Sparse (Fin 3237) := [(586, 1), (1238, 1), (1349, 1), (1467, 1), (1469, 1), (1476, 1), (2832, -1)]

def row1844 : Integer.Sparse (Fin 3237) := [(0, 81), (32, 15), (160, -240), (218, 720), (225, -240), (260, 180), (261, 510), (436, -12960), (439, -6480), (441, -6480), (495, -12960), (496, -6480), (505, -12960), (512, -6480), (1212, -12960), (1226, -12960), (1229, -6480), (1231, -6480), (1277, -12960), (1280, -12960), (1309, -12960), (1310, -12960), (1318, -25920), (1324, -12960), (1462, -25920), (1464, -12960), (1471, -12960), (1473, -6480), (1476, -6480), (1516, -12960), (1518, -6480), (1528, -6480), (1616, -12960), (1617, -6480), (1620, -12960), (1628, -6480), (2643, -12960), (2701, -12960), (2750, -12960), (2754, -6480), (2766, -6480)]

def row1845 : Integer.Sparse (Fin 3237) := [(0, -81), (32, -15), (160, 240), (218, -720), (225, 240), (260, -180), (261, -510), (436, 12960), (439, 6480), (441, 6480), (505, 6480), (1212, 12960), (1226, 12960), (1229, 6480), (1231, 6480), (1277, 12960), (1280, 12960), (1318, 12960), (1462, 12960), (1464, 6480), (1471, 12960), (1473, 6480), (1617, 6480), (1620, 6480), (2643, 12960), (2750, 6480)]

def row1846 : Integer.Sparse (Fin 3237) := [(0, -116), (3, 160), (32, -80), (66, 320), (159, -960), (160, 320), (261, -220), (1084, 17280), (1096, 8640), (1097, 8640), (1104, 8640), (1397, 17280), (1429, 8640), (1433, 17280), (1442, 17280), (1443, 17280), (1454, 17280), (1455, 17280), (1475, 8640), (1477, 8640), (1482, 17280), (1496, 8640), (1497, 8640), (1857, 17280), (1874, 8640)]

def row1847 : Integer.Sparse (Fin 3237) := [(0, -120), (3, 200), (32, -130), (219, 480), (261, -10), (915, 4320), (917, 2160), (918, 2160), (2033, 4320), (2038, 4320), (2053, 2160), (2054, 2160), (2055, 2160), (2207, 4320), (2215, 4320), (2216, 2160), (2217, 2160), (2223, 4320), (2226, 4320)]

def row1848 : Integer.Sparse (Fin 3237) := [(663, -1), (1177, -1), (1398, -2), (1468, -4), (1473, -2), (1578, -2), (1608, -4), (1628, -2), (1979, -2), (2538, -2), (2888, 8), (2893, 8), (2998, 8), (3002, 8), (3012, 8), (3015, 16), (3183, 8), (3199, 4)]

def row1849 : Integer.Sparse (Fin 3237) := [(0, -104), (3, -40), (32, -80), (251, 480), (261, -160), (882, 2880), (884, 2880), (1656, 5760), (1662, 2880), (2188, 2880), (2190, 1440), (2196, 2880), (2220, 2880)]

def row1850 : Integer.Sparse (Fin 3237) := [(1153, 2), (1174, 2), (1177, 1), (1557, 2), (1576, 4), (1578, 2), (1605, 2), (1608, 4), (1627, 2), (1628, 2), (1945, 2), (1976, 1), (1979, 2)]

def row1851 : Integer.Sparse (Fin 3237) := [(1239, 2), (1243, 2), (1477, 1), (2190, 1), (2831, -1)]

def row1852 : Integer.Sparse (Fin 3237) := [(587, 1), (1239, 1), (1350, 1), (1468, 2), (1477, 1), (2831, -1)]

def row1853 : Integer.Sparse (Fin 3237) := [(0, 81), (32, 15), (160, -240), (222, 360), (256, -240), (260, 90), (261, -120), (437, -6480), (440, -6480), (506, -3240), (509, -6480), (511, -6480), (519, -3240), (1227, -6480), (1230, -6480), (1278, -6480), (1279, -12960), (1319, -6480), (1321, -6480), (1323, -12960), (1330, -6480), (1468, -12960), (1470, -6480), (1525, -6480), (1527, -6480), (1608, -12960), (1609, -6480), (1611, -6480), (1619, -6480), (2685, -6480), (2705, -6480), (2755, -3240), (2769, -6480)]

def row1854 : Integer.Sparse (Fin 3237) := [(0, -81), (32, -15), (160, 240), (222, -360), (256, 240), (260, -90), (261, 120), (437, 6480), (440, 6480), (506, 3240), (1227, 6480), (1230, 6480), (1278, 6480), (1279, 12960), (1319, 6480), (1468, 12960), (1470, 6480), (1619, 6480), (2685, 6480)]

def row1855 : Integer.Sparse (Fin 3237) := [(0, 6), (3, -5), (71, -20), (261, -5), (687, -1080), (1097, -1080), (1398, -1080), (1417, -2160), (1443, -2160), (1476, -1080), (1578, -1080), (1617, -1080), (2055, -1080), (2565, -540), (2577, -1080), (2934, 4320), (2939, 2160), (3037, 4320), (3042, 4320), (3052, 8640), (3062, 4320), (3145, 4320)]

def row1856 : Integer.Sparse (Fin 3237) := [(0, -104), (3, 120), (32, -60), (71, 160), (159, -960), (261, 100), (1085, 8640), (1097, 8640), (1105, 4320), (1398, 8640), (1434, 8640), (1443, 17280), (1455, 17280), (1476, 8640), (1483, 8640), (1497, 8640), (1858, 8640)]

def row1857 : Integer.Sparse (Fin 3237) := [(1275, 1), (1279, 1), (1280, 1), (1443, 1), (2418, 1), (2828, -1)]

def row1858 : Integer.Sparse (Fin 3237) := [(572, -1), (662, -1), (1121, -1), (1164, -1), (1226, -1), (1342, -1), (1388, -1), (1391, -1), (1397, -1), (1424, -1), (1476, -1), (1516, -1), (1536, -1), (1548, -1), (1561, -1), (1568, -1), (1569, -1), (1611, -1), (1617, -1), (1619, -1), (1933, -1), (2490, -1), (2867, 4), (2872, 4), (2874, 4), (2977, 4), (2979, 4), (2981, 4), (2983, 4), (2989, 4), (3003, 4), (3011, 4), (3014, 4), (3026, 4), (3028, 4), (3163, 4), (3167, 4), (3178, 4), (3180, 4)]

def row1859 : Integer.Sparse (Fin 3237) := [(0, -114), (3, -60), (32, 155), (66, 80), (68, 80), (160, 80), (162, 80), (219, -240), (261, 125), (889, 1440), (890, 1440), (892, 1440), (1206, 1440), (1210, 1440), (1225, 1440), (1453, 1440), (1986, 1440), (1989, 1440), (2000, 1440), (2138, 1440), (2147, 1440), (2148, 1440), (2153, 1440), (2198, 1440), (2219, 1440), (2238, 1440)]

def row1860 : Integer.Sparse (Fin 3237) := [(1108, 1), (1119, 1), (1121, 1), (1125, 1), (1164, 1), (1503, 1), (1514, 1), (1516, 1), (1519, 1), (1520, 1), (1521, 1), (1535, 1), (1536, 1), (1548, 1), (1552, 1), (1553, 1), (1561, 1), (1565, 1), (1568, 1), (1569, 1), (1573, 1), (1617, 1), (1619, 1), (1901, 1), (1914, 1), (1933, 1), (1939, 1), (1941, 1)]

def row1861 : Integer.Sparse (Fin 3237) := [(1204, 1), (1208, 1), (1210, 1), (1226, 1), (1397, 1), (2359, 1), (2832, -1)]

def row1862 : Integer.Sparse (Fin 3237) := [(572, 1), (1226, 1), (1342, 1), (1397, 1), (1424, 1), (2832, -1)]

def row1863 : Integer.Sparse (Fin 3237) := [(550, 1), (1204, 1), (1349, 1), (1388, 1), (1390, 1), (1397, 1), (2832, -1)]

def row1864 : Integer.Sparse (Fin 3237) := [(0, 198), (3, 60), (32, 30), (66, 240), (160, 960), (218, -720), (225, 720), (260, -180), (261, -120), (412, -12960), (415, -12960), (417, -12960), (424, -12960), (450, -12960), (451, -12960), (453, -12960), (458, -12960), (474, -12960), (498, -12960), (1185, -12960), (1187, -12960), (1189, -12960), (1196, -12960), (1199, -12960), (1216, -12960), (1252, -12960), (1253, -12960), (1255, -12960), (1260, -12960), (1266, -12960), (1270, -12960), (1283, -12960), (1284, -12960), (1287, -12960), (1295, -12960), (1311, -12960), (1342, -12960), (1345, -12960), (1385, -12960), (1387, -25920), (1392, -12960), (1394, -12960), (1397, -12960), (1417, -12960), (1424, -12960), (1436, -12960), (1443, -12960), (1467, -12960), (1502, -12960), (1536, -12960), (1545, -12960), (1567, -12960), (1568, -12960), (1569, -12960), (1577, -12960), (1590, -12960), (1593, -12960), (1618, -12960), (2610, -12960), (2633, -12960), (2668, -12960), (2689, -12960), (2727, -25920), (2752, -12960), (2765, -12960)]

def row1865 : Integer.Sparse (Fin 3237) := [(573, -1), (663, -1), (1131, -1), (1177, -1), (1227, -1), (1343, -1), (1389, -2), (1394, -2), (1398, -1), (1477, -1), (1525, -1), (1542, -1), (1560, -2), (1577, -2), (1578, -1), (1629, -1), (1948, -2), (2491, -2), (2873, 8), (2978, 4), (2982, 8), (3004, 8), (3012, 4), (3015, 8), (3166, 4), (3183, 4)]

def row1866 : Integer.Sparse (Fin 3237) := [(0, -196), (3, -160), (32, -160), (71, 160), (251, -480), (261, -220), (891, 4320), (1641, 4320), (1645, 4320), (1656, 4320), (2188, 2160), (2189, 2160), (2199, 2160), (2220, 2160)]

def row1867 : Integer.Sparse (Fin 3237) := [(1129, 2), (1131, 1), (1177, 1), (1507, 1), (1523, 2), (1525, 1), (1540, 2), (1542, 1), (1557, 1), (1560, 2), (1576, 2), (1577, 2), (1578, 1), (1629, 1), (1905, 1), (1945, 1), (1948, 2)]

def row1868 : Integer.Sparse (Fin 3237) := [(1205, 1), (1209, 2), (1227, 1), (1398, 1), (2360, 1), (2831, -1)]

def row1869 : Integer.Sparse (Fin 3237) := [(573, 1), (1227, 1), (1343, 1), (1398, 1), (2831, -1)]

def row1870 : Integer.Sparse (Fin 3237) := [(1205, 1), (1350, 1), (1389, 2), (1398, 1), (2831, -1)]

def row1871 : Integer.Sparse (Fin 3237) := [(0, 216), (3, 30), (32, 75), (71, 120), (160, 240), (222, -360), (256, 240), (260, -90), (261, -165), (413, -6480), (416, -12960), (425, -6480), (455, -6480), (457, -12960), (461, -6480), (475, -6480), (515, -6480), (1186, -6480), (1188, -12960), (1197, -6480), (1257, -6480), (1259, -12960), (1262, -6480), (1265, -12960), (1271, -6480), (1286, -12960), (1289, -6480), (1296, -6480), (1326, -6480), (1343, -6480), (1344, -12960), (1389, -12960), (1391, -12960), (1398, -6480), (1422, -12960), (1542, -6480), (1544, -12960), (1560, -12960), (1561, -12960), (1562, -12960), (1578, -6480), (1592, -12960), (1610, -12960), (2611, -6480), (2671, -6480), (2674, -6480), (2691, -6480), (2759, -6480), (2764, -12960)]

def row1872 : Integer.Sparse (Fin 3237) := [(0, 6), (3, -5), (71, -20), (261, -5), (619, -1080), (1054, -1080), (1296, -540), (1319, -540), (1326, -540), (1330, -540), (1361, -1080), (1368, -1080), (1397, -1080), (1398, -540), (1477, -540), (1568, -1080), (1578, -540), (1629, -540), (1761, -540), (2087, -1080), (2450, -540), (2561, -1080), (2565, -540), (2906, 2160), (2934, 2160), (3018, 2160), (3023, 4320), (3035, 4320), (3037, 2160), (3052, 4320)]

def row1873 : Integer.Sparse (Fin 3237) := [(577, -1), (700, -1), (1123, -1), (1167, -1), (1216, -2), (1229, -1), (1421, -2), (1429, -2), (1502, -2), (1518, -1), (1551, -2), (1571, -2), (1622, -1), (1632, -1), (1936, -1), (2502, -1), (2877, 8), (2881, 4), (2988, 8), (2991, 4), (2999, 8), (3006, 8), (3040, 8), (3043, 4), (3157, 8), (3165, 4), (3182, 4)]

def row1874 : Integer.Sparse (Fin 3237) := [(0, -114), (3, -40), (32, -550), (68, -160), (162, -160), (261, -20), (897, 2880), (898, 1440), (1240, 2880), (1244, 1440), (1495, 1440), (1928, 2880), (1943, 1440), (2139, 2880), (2141, 2880), (2154, 1440), (2166, 2880)]

def row1875 : Integer.Sparse (Fin 3237) := [(1110, 2), (1123, 1), (1127, 1), (1167, 1), (1502, 2), (1505, 2), (1518, 1), (1522, 1), (1530, 2), (1539, 2), (1551, 2), (1555, 2), (1571, 2), (1575, 1), (1622, 1), (1890, 2), (1903, 1), (1936, 1), (1943, 1)]

def row1876 : Integer.Sparse (Fin 3237) := [(1221, 2), (1229, 1), (1232, 1), (1429, 1), (2375, 1), (2833, -1)]

def row1877 : Integer.Sparse (Fin 3237) := [(567, -2), (578, -1), (579, -1), (1115, -2), (1133, -1), (1134, -1), (1222, -2), (1230, -1), (1231, -1), (1339, -2), (1344, -2), (1345, -2), (1422, -2), (1426, -1), (1511, -2), (1527, -1), (1528, -1), (1533, -2), (1544, -2), (1545, -2), (1562, -2), (1580, -1), (1909, -1), (1920, -2), (1950, -1), (2376, -1), (2460, -2), (2503, -1), (2832, 4)]

def row1878 : Integer.Sparse (Fin 3237) := [(1115, 2), (1133, 1), (1134, 1), (1511, 2), (1527, 1), (1528, 1), (1533, 2), (1544, 2), (1545, 2), (1562, 2), (1580, 1), (1909, 1), (1920, 2), (1950, 1), (2832, 1)]

def row1879 : Integer.Sparse (Fin 3237) := [(1222, 2), (1230, 1), (1231, 1), (2376, 1), (2832, -1)]

def row1880 : Integer.Sparse (Fin 3237) := [(524, -1), (531, -1), (532, -1), (605, -1), (1021, -1), (1033, -1), (1034, -1), (1066, -1), (1183, -1), (1188, -1), (1189, -1), (1248, -1), (1259, -1), (1260, -1), (1265, -1), (1266, -1), (1275, -1), (1279, -1), (1280, -1), (1286, -1), (1287, -1), (1301, -1), (1303, -2), (1306, -1), (1323, -1), (1324, -1), (1328, -1), (1361, -1), (1368, -1), (1417, -1), (1422, -1), (1443, -1), (1562, -1), (1696, -1), (1735, -1), (1777, -1), (1782, -1), (2335, -1), (2402, -1), (2418, -1), (2439, -1), (2828, 4)]

def row1881 : Integer.Sparse (Fin 3237) := [(533, -1), (535, -1), (539, -1), (619, -1), (1019, -1), (1025, -1), (1029, -1), (1054, -1), (1190, -1), (1192, -1), (1196, -1), (1246, -1), (1251, -1), (1255, -1), (1267, -1), (1270, -1), (1282, -1), (1284, -1), (1295, -1), (1296, -1), (1308, -1), (1311, -1), (1314, -1), (1318, -2), (1319, -1), (1326, -1), (1330, -1), (1361, -1), (1368, -1), (1397, -1), (1398, -1), (1568, -1), (1578, -1), (1684, -1), (1728, -1), (1760, -1), (1761, -1), (2344, -1), (2406, -1), (2446, -1), (2450, -1), (2830, 4)]

def row1882 : Integer.Sparse (Fin 3237) := [(2813, 2), (2815, 2), (2819, 1), (2822, 4), (2823, 2), (2824, 2), (2826, 2), (2828, 4), (2829, 2), (2830, 2), (2832, 2), (2836, 2), (2837, 1), (2840, 2)]

def row1883 : Integer.Sparse (Fin 3237) := [(564, 1), (1218, 1), (1390, 1), (1403, 1), (1420, 1), (1424, 1), (2832, -1)]

def row1884 : Integer.Sparse (Fin 3237) := [(1723, 1), (2166, 1), (2231, 1), (2238, 2), (2684, 1), (2839, -1)]

def row1885 : Integer.Sparse (Fin 3237) := [(1215, 1), (1402, 1), (1420, 1), (1422, 2), (2832, -1)]

def row1886 : Integer.Sparse (Fin 3237) := [(2059, 1), (2220, 2), (2225, 1), (2235, 1), (2788, 1), (2839, -1)]

def row1887 : Integer.Sparse (Fin 3237) := [(1714, 1), (2218, 1), (2219, 1), (2224, 1), (2234, 1), (2677, 1), (2840, -1)]

def row1888 : Integer.Sparse (Fin 3237) := [(1726, 1), (2141, 1), (2200, 1), (2202, 1), (2230, 1), (2643, 1), (2840, -1)]

def row1889 : Integer.Sparse (Fin 3237) := [(582, 1), (1234, 1), (1449, 1), (1466, 1), (1468, 2), (2831, -1)]

def row1890 : Integer.Sparse (Fin 3237) := [(2056, 1), (2199, 2), (2201, 1), (2225, 1), (2635, 1), (2839, -1)]

def row1891 : Integer.Sparse (Fin 3237) := [(584, 1), (1236, 1), (1450, 2), (1466, 1), (1471, 1), (2831, -1)]

def row1892 : Integer.Sparse (Fin 3237) := [(1707, 1), (2197, 1), (2198, 1), (2200, 1), (2224, 1), (2633, 1), (2840, -1)]

def row1893 : Integer.Sparse (Fin 3237) := [(2062, 1), (2192, 1), (2196, 2), (2214, 1), (2373, 1), (2831, -1)]

def row1894 : Integer.Sparse (Fin 3237) := [(1719, 1), (2191, 1), (2193, 1), (2195, 1), (2212, 1), (2370, 1), (2832, -1)]

def row1895 : Integer.Sparse (Fin 3237) := [(734, 1), (1650, 1), (1754, 1), (1766, 1), (1780, 1), (1784, 1), (2840, -1)]

def row1896 : Integer.Sparse (Fin 3237) := [(1721, 1), (2063, 1), (2064, 1), (2097, 1), (2116, 1), (2682, 1), (2839, -1)]

def row1897 : Integer.Sparse (Fin 3237) := [(731, 1), (1765, 1), (1780, 1), (1782, 2), (2840, -1)]

def row1898 : Integer.Sparse (Fin 3237) := [(2020, 1), (2022, 2), (2050, 1), (2109, 1), (2775, 1), (2839, -1)]

def row1899 : Integer.Sparse (Fin 3237) := [(1710, 1), (2019, 1), (2021, 1), (2047, 1), (2107, 1), (2676, 1), (2840, -1)]

def row1900 : Integer.Sparse (Fin 3237) := [(1337, 1), (1711, 2), (1781, 1), (2456, 1), (2832, -1)]

def row1901 : Integer.Sparse (Fin 3237) := [(1710, 1), (1712, 1), (1717, 1), (1782, 1), (2676, 1), (2840, -1)]

def row1902 : Integer.Sparse (Fin 3237) := [(1714, 1), (1715, 1), (1717, 1), (1784, 1), (1811, 1), (2677, 1), (2840, -1)]

def row1903 : Integer.Sparse (Fin 3237) := [(893, 1), (2008, 1), (2081, 1), (2088, 1), (2095, 1), (2097, 1), (2839, -1)]

def row1904 : Integer.Sparse (Fin 3237) := [(0, 106), (4, 5), (32, 5), (66, -80), (160, -80), (261, 530), (739, -1080), (740, -1080), (742, -2160), (1998, -1080), (1999, -1080), (2001, -2160), (2060, -2160), (2097, -2160), (2279, -1080), (2280, -2160), (2283, -1080), (2318, -1080), (2540, -1080), (2543, -1080), (2546, -2160), (2550, -2160), (2554, -3240), (2556, -2160), (2558, -2160), (2563, -2160), (2571, -1080), (2752, -1080), (2756, -1080), (2763, -1080)]

def row1905 : Integer.Sparse (Fin 3237) := [(0, -106), (4, -5), (32, -5), (66, 80), (160, 80), (261, -530), (739, 1080), (740, 1080), (742, 2160), (1998, 1080), (1999, 1080), (2001, 2160), (2060, 2160), (2097, 2160)]

def row1906 : Integer.Sparse (Fin 3237) := [(0, 38), (4, 1), (32, 1), (66, -16), (160, -16), (261, -26), (561, -432), (562, -432), (567, -864), (653, -432), (1106, -432), (1107, -432), (1115, -864), (1142, -432), (1337, -432), (1344, -432), (1391, -864), (1532, -432), (1544, -432), (1561, -864), (1648, -432), (1653, -864), (1712, -864), (1752, -432), (1808, -864), (1815, -864), (1933, -864), (2382, -432), (2388, -864), (2420, -864), (2429, -432), (2475, -864), (2481, -864), (2490, -864), (2553, -432), (2557, -864), (2570, -432), (2757, -432), (2759, -432), (2764, -864)]

def row1907 : Integer.Sparse (Fin 3237) := [(0, -38), (4, -1), (32, -1), (66, 16), (160, 16), (261, 26), (561, 432), (562, 432), (567, 864), (653, 432), (1337, 432), (1344, 432), (1391, 864), (1648, 432), (1653, 864), (1712, 864), (1752, 432), (1808, 864), (1815, 864), (1933, 864)]

def row1908 : Integer.Sparse (Fin 3237) := [(0, 133), (4, 5), (32, -30), (71, -80), (261, -160), (733, -1080), (735, -1080), (738, -1080), (743, -1080), (1713, -1080), (1718, -1080), (1758, -1080), (1993, -1080), (1997, -1080), (2002, -1080), (2058, -1080), (2087, -1080), (2273, -1080), (2274, -1080), (2275, -1080), (2284, -1080), (2319, -1080), (2425, -1080), (2427, -1080), (2449, -1080), (2542, -1080), (2547, -1080), (2548, -1080), (2551, -1080), (2553, -1080), (2557, -3240), (2561, -1080), (2562, -1080), (2564, -1080), (2565, -1080), (2575, -1080), (2753, -1080), (2757, -1080), (2764, -1080)]

def row1909 : Integer.Sparse (Fin 3237) := [(0, -133), (4, -5), (32, 30), (71, 80), (261, 160), (733, 1080), (735, 1080), (738, 1080), (743, 1080), (1713, 1080), (1718, 1080), (1758, 1080), (1993, 1080), (1997, 1080), (2002, 1080), (2058, 1080), (2087, 1080)]

def row1910 : Integer.Sparse (Fin 3237) := [(0, 181), (4, 5), (32, -30), (71, -80), (261, 80), (563, -1440), (565, -1440), (567, -1440), (573, -1440), (654, -1440), (1113, -1440), (1114, -1440), (1115, -1440), (1131, -1440), (1156, -1440), (1649, -1440), (1651, -1440), (1653, -1440), (1658, -1440), (1709, -1440), (1712, -1440), (1716, -1440), (1753, -1440), (1755, -1440), (1810, -1440), (1815, -1440), (1934, -1440), (2386, -1440), (2387, -1440), (2388, -1440), (2397, -1440), (2419, -1440), (2420, -1440), (2426, -1440), (2437, -1440), (2438, -1440), (2480, -1440), (2481, -1440), (2501, -1440), (2553, -1440), (2554, -1440), (2557, -2880), (2558, -1440), (2565, -1440), (2570, -1440), (2575, -1440), (2799, -1440), (2801, -1440), (2803, -1440)]

def row1911 : Integer.Sparse (Fin 3237) := [(0, -181), (4, -5), (32, 30), (71, 80), (261, -80), (563, 1440), (565, 1440), (567, 1440), (573, 1440), (654, 1440), (1649, 1440), (1651, 1440), (1653, 1440), (1658, 1440), (1709, 1440), (1712, 1440), (1716, 1440), (1753, 1440), (1755, 1440), (1810, 1440), (1815, 1440), (1934, 1440)]

def row1912 : Integer.Sparse (Fin 3237) := [(1758, -1), (2081, -1), (2087, -1), (2177, -1), (2449, -1), (2555, -1), (2561, -1), (2573, -1), (2682, -1), (2685, -1), (2697, -1), (2705, -1), (2729, -1), (2742, -1), (2793, -2), (2875, 4), (2876, 4), (2877, 4), (2879, 4), (2920, 4), (3073, 4), (3074, 4), (3075, 4), (3076, 4), (3095, 4), (3096, 4), (3097, 4), (3108, 4), (3125, 4), (3126, 4), (3127, 4), (3134, 4), (3135, 4), (3136, 4), (3175, 4), (3194, 4)]

def row1913 : Integer.Sparse (Fin 3237) := [(1109, 1), (1110, 1), (1116, 1), (1122, 1), (1149, 1), (1880, 1), (1886, 1), (1894, 1), (1931, 1), (2384, 1), (2389, 1), (2394, 1), (2421, 1), (2424, 1), (2433, 1), (2449, 1), (2477, 1), (2482, 1), (2497, 1), (2513, 1), (2520, 1), (2527, 1), (2555, 1), (2561, 1), (2573, 1), (2697, 1), (2705, 1), (2729, 1), (2793, 1)]

def row1914 : Integer.Sparse (Fin 3237) := [(0, 143), (4, 5), (32, -50), (66, -80), (160, -160), (261, -110), (730, -1440), (732, -1440), (738, -2880), (1340, -1440), (1345, -1440), (1394, -2880), (1541, -1440), (1543, -1440), (1545, -1440), (1577, -2880), (1992, -1440), (1997, -2880), (2058, -2880), (2081, -2880), (2087, -2880), (2266, -1440), (2275, -2880), (2318, -1440), (2545, -1440), (2548, -2880), (2551, -2880), (2553, -1440), (2555, -2880), (2557, -2880), (2561, -2880), (2562, -1440), (2578, -2880), (2752, -1440), (2758, -1440), (2765, -2880)]

def row1915 : Integer.Sparse (Fin 3237) := [(0, -143), (4, -5), (32, 50), (66, 80), (160, 160), (261, 110), (730, 1440), (732, 1440), (738, 2880), (1340, 1440), (1345, 1440), (1394, 2880), (1992, 1440), (1997, 2880), (2058, 2880), (2081, 2880), (2087, 2880)]

def row1916 : Integer.Sparse (Fin 3237) := [(0, 143), (4, 5), (32, -50), (66, -80), (160, -160), (261, -110), (569, -1440), (570, -1440), (572, -2880), (657, -1440), (1120, -1440), (1121, -2880), (1130, -1440), (1163, -1440), (1654, -1440), (1655, -1440), (1657, -2880), (1713, -1440), (1715, -2880), (1756, -1440), (1836, -1440), (1837, -2880), (1968, -1440), (2392, -1440), (2393, -2880), (2396, -1440), (2423, -2880), (2425, -1440), (2445, -1440), (2518, -1440), (2519, -2880), (2536, -1440), (2562, -2880), (2563, -2880), (2564, -2880), (2578, -2880), (2757, -1440), (2759, -1440), (2794, -1440)]

def row1917 : Integer.Sparse (Fin 3237) := [(0, -143), (4, -5), (32, 50), (66, 80), (160, 160), (261, 110), (569, 1440), (570, 1440), (572, 2880), (657, 1440), (1654, 1440), (1655, 1440), (1657, 2880), (1713, 1440), (1715, 2880), (1756, 1440), (1836, 1440), (1837, 2880), (1968, 1440)]

def row1918 : Integer.Sparse (Fin 3237) := [(0, 132), (4, -15), (32, 55), (66, 80), (71, 160), (160, 80), (261, 150), (1392, -4320), (1424, -8640), (1471, -4320), (1567, -4320), (1569, -8640), (1616, -4320), (1752, -4320), (1756, -4320), (1781, -4320), (1784, -8640), (1810, -4320), (1919, -4320), (2047, -8640), (2081, -8640), (2097, -8640), (2429, -4320), (2445, -4320), (2447, -8640), (2480, -4320), (2554, -4320), (2555, -8640), (2556, -8640), (2557, -8640), (2572, -8640), (3125, 34560), (3132, 17280), (3137, 34560), (3143, 17280), (3150, 17280)]

def row1919 : Integer.Sparse (Fin 3237) := [(760, 1), (1669, 1), (1808, 1), (1819, 1), (1834, 1), (1837, 1), (2840, -1)]

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

def row1920 : Integer.Sparse (Fin 3237) := [(2059, 1), (2060, 1), (2061, 1), (2084, 2), (2788, 1), (2839, -1)]

def row1921 : Integer.Sparse (Fin 3237) := [(762, 1), (1670, 1), (1810, 1), (1820, 2), (1836, 1), (2839, -1)]

def row1922 : Integer.Sparse (Fin 3237) := [(2020, 1), (2058, 1), (2061, 1), (2082, 2), (2775, 1), (2839, -1)]

def row1923 : Integer.Sparse (Fin 3237) := [(2079, 1), (2648, 1), (2651, 1), (2658, 1), (2732, 1), (2790, 1), (2835, -1)]

def row1924 : Integer.Sparse (Fin 3237) := [(1713, -1), (1758, -1), (2058, -1), (2060, -1), (2081, -1), (2087, -1), (2097, -1), (2177, -1), (2425, -1), (2449, -1), (2550, -1), (2551, -1), (2555, -1), (2556, -1), (2561, -1), (2573, -1), (2674, -1), (2691, -1), (2717, -1), (2722, -1), (2791, -2), (2866, 4), (2867, 4), (2870, 4), (2875, 4), (2910, 4), (3068, 4), (3069, 4), (3070, 4), (3073, 4), (3122, 4), (3123, 4), (3125, 4), (3128, 4), (3129, 4), (3134, 4), (3170, 4), (3189, 4)]

def row1925 : Integer.Sparse (Fin 3237) := [(0, -386), (1, 200), (2, -10), (3, -400), (4, -10), (31, -600), (32, 850), (34, 480), (35, 160), (37, 320), (66, 960), (68, 320), (71, 1280), (153, -960), (154, -480), (156, -960), (159, -960), (160, 2720), (162, 160), (165, 320), (218, -480), (222, -960), (225, 480), (251, -480), (255, 320), (256, 1120), (260, 240), (261, -1420), (273, -480), (274, -480), (549, 8640), (550, 8640), (553, 8640), (564, 8640), (635, 8640), (1639, 8640), (1640, 8640), (1642, 8640), (1650, 8640), (1801, 8640), (1803, 8640), (1811, 8640), (1819, 8640), (1820, 8640), (1834, 8640), (1924, 8640), (1957, 8640)]

def row1926 : Integer.Sparse (Fin 3237) := [(1108, 1), (1109, 1), (1111, 1), (1118, 1), (1148, 1), (2383, 1), (2384, 1), (2385, 1), (2390, 1), (2425, 1), (2449, 1), (2476, 1), (2477, 1), (2479, 1), (2496, 1), (2512, 1), (2513, 1), (2517, 1), (2526, 1), (2550, 1), (2551, 1), (2555, 1), (2556, 1), (2561, 1), (2573, 1), (2691, 1), (2722, 1), (2791, 1)]

def row1927 : Integer.Sparse (Fin 3237) := [(1706, 1), (2006, 1), (2007, 1), (2008, 1), (2081, 1), (2674, 1), (2839, -1)]

def row1928 : Integer.Sparse (Fin 3237) := [(765, 1), (1673, 1), (1824, 3), (1836, 1), (2839, -1)]

def row1929 : Integer.Sparse (Fin 3237) := [(1340, 1), (2057, 2), (2080, 2), (2458, 1), (2831, -1)]

def row1930 : Integer.Sparse (Fin 3237) := [(1986, 1), (1987, 2), (1998, 1), (2031, 1), (2609, 1), (2839, -1)]

def row1931 : Integer.Sparse (Fin 3237) := [(1983, 1), (1985, 1), (1987, 1), (1993, 1), (2030, 1), (2607, 1), (2839, -1)]

def row1932 : Integer.Sparse (Fin 3237) := [(1790, 1), (1984, 2), (1992, 1), (2029, 1), (2606, 1), (2840, -1)]

def row1933 : Integer.Sparse (Fin 3237) := [(1400, 2), (1405, 1), (1415, 1), (1616, 1), (2494, 1), (2828, -1)]

def row1934 : Integer.Sparse (Fin 3237) := [(1994, 1), (2000, 1), (2001, 1), (2003, 1), (2051, 1), (2622, 1), (2840, -1)]

def row1935 : Integer.Sparse (Fin 3237) := [(1993, -1), (1999, -1), (2002, -2), (2046, -1), (2050, -2), (2159, -1), (2542, -1), (2543, -1), (2547, -2), (2566, -1), (2567, -1), (2569, -2), (2775, -1), (2779, -1), (2783, -2), (2786, -2), (2883, 4), (2884, 4), (2888, 8), (2927, 4), (3098, 4), (3100, 8), (3112, 4), (3131, 8), (3142, 8), (3145, 8), (3180, 8)]

def row1936 : Integer.Sparse (Fin 3237) := [(1139, 1), (1140, 1), (1144, 1), (1153, 2), (2428, 1), (2431, 1), (2435, 2), (2487, 2), (2488, 2), (2492, 2), (2499, 2), (2542, 1), (2543, 1), (2547, 2), (2566, 1), (2567, 1), (2569, 2), (2779, 1), (2786, 2)]

def row1937 : Integer.Sparse (Fin 3237) := [(1718, -1), (1786, -1), (1992, -1), (1997, -1), (2001, -1), (2047, -1), (2055, -1), (2160, -1), (2427, -1), (2451, -1), (2545, -1), (2546, -1), (2548, -1), (2572, -1), (2574, -1), (2577, -1), (2676, -1), (2688, -1), (2723, -2), (2783, -1), (2786, -1), (2885, 4), (2886, 4), (2887, 4), (2891, 4), (2928, 4), (3095, 4), (3099, 4), (3101, 4), (3113, 4), (3126, 4), (3143, 4), (3144, 4), (3146, 4), (3147, 4), (3148, 4), (3181, 4), (3197, 4)]

def row1938 : Integer.Sparse (Fin 3237) := [(1146, 1), (1147, 1), (1150, 1), (1152, 1), (1160, 1), (2421, 1), (2427, 1), (2432, 1), (2434, 1), (2442, 1), (2451, 1), (2482, 1), (2494, 1), (2495, 1), (2498, 1), (2524, 1), (2525, 1), (2528, 1), (2533, 1), (2545, 1), (2546, 1), (2548, 1), (2572, 1), (2574, 1), (2577, 1), (2688, 1), (2723, 1), (2783, 1)]

def row1939 : Integer.Sparse (Fin 3237) := [(1345, 1), (1991, 1), (1996, 2), (2045, 1), (2460, 1), (2832, -1)]

def row1940 : Integer.Sparse (Fin 3237) := [(1844, 1), (2170, 1), (2651, 1), (2732, 2), (2733, 1), (2835, -1)]

def row1941 : Integer.Sparse (Fin 3237) := [(866, -1), (1755, -1), (1808, -1), (1815, -1), (1837, -1), (1969, -1), (1979, -1), (2315, -1), (2438, -1), (2475, -1), (2481, -1), (2519, -1), (2537, -1), (2538, -1), (2643, -1), (2681, -1), (2692, -1), (2701, -1), (2727, -2), (2729, -1), (2742, -1), (2953, 4), (2954, 4), (2955, 4), (2957, 4), (3083, 4), (3085, 4), (3086, 4), (3088, 4), (3098, 4), (3120, 4), (3121, 4), (3128, 4), (3131, 4), (3133, 4), (3134, 4), (3136, 4), (3137, 4)]

def row1942 : Integer.Sparse (Fin 3237) := [(1883, 1), (1885, 1), (1887, 1), (1904, 1), (1944, 1), (2269, 1), (2276, 1), (2281, 1), (2315, 1), (2428, 1), (2438, 1), (2443, 1), (2475, 1), (2481, 1), (2488, 1), (2508, 1), (2510, 1), (2511, 1), (2512, 1), (2513, 1), (2519, 1), (2520, 1), (2537, 1), (2538, 1), (2692, 1), (2701, 1), (2727, 1), (2742, 1)]

def row1943 : Integer.Sparse (Fin 3237) := [(1669, 1), (1671, 1), (1672, 1), (1674, 1), (1837, 1), (2643, 1), (2840, -1)]

def row1944 : Integer.Sparse (Fin 3237) := [(0, 152), (3, -40), (4, -5), (32, 65), (66, -80), (160, -80), (261, -30), (558, -4320), (559, -4320), (560, -4320), (572, -4320), (649, -4320), (1076, -4320), (1077, -4320), (1078, -4320), (1089, -4320), (1121, -4320), (1274, -4320), (1279, -4320), (1300, -4320), (1308, -4320), (1314, -4320), (1323, -4320), (1470, -4320), (1609, -4320), (1646, -4320), (1647, -4320), (1657, -4320), (1708, -4320), (1715, -4320), (1750, -4320), (1796, -4320), (1799, -4320), (1836, -4320), (1837, -8640), (1896, -4320), (1968, -4320), (1969, -4320), (2351, -4320), (2352, -4320), (2370, -4320), (2380, -4320), (2381, -4320), (2393, -4320), (2410, -4320), (2414, -4320), (2423, -4320), (2518, -4320), (2519, -8640), (2536, -4320), (2537, -4320), (2562, -4320), (2563, -4320), (2682, -4320), (2685, -4320), (2697, -4320), (2699, -4320), (2703, -4320), (2705, -4320), (2769, -4320), (2794, -4320)]

def row1945 : Integer.Sparse (Fin 3237) := [(826, -1), (1713, -1), (1716, -2), (1810, -2), (1836, -1), (1934, -2), (2309, -1), (2425, -1), (2426, -2), (2480, -2), (2501, -2), (2518, -1), (2635, -1), (2715, -1), (2717, -2), (2722, -2), (2941, 4), (2944, 8), (2952, 4), (3079, 4), (3081, 8), (3084, 4), (3122, 8), (3129, 8)]

def row1946 : Integer.Sparse (Fin 3237) := [(2265, 1), (2267, 1), (2271, 2), (2309, 1), (2425, 1), (2426, 2), (2472, 1), (2473, 2), (2479, 2), (2480, 2), (2501, 2), (2509, 1), (2517, 2), (2518, 1), (2715, 1), (2722, 2)]

def row1947 : Integer.Sparse (Fin 3237) := [(1665, 1), (1667, 2), (1670, 1), (1810, 1), (2635, 1), (2839, -1)]

def row1948 : Integer.Sparse (Fin 3237) := [(0, 322), (4, 5), (32, -45), (66, -80), (160, -240), (256, -160), (545, -4320), (546, -8640), (563, -4320), (600, -4320), (1041, -4320), (1042, -8640), (1064, -4320), (1113, -4320), (1637, -4320), (1638, -8640), (1649, -4320), (1676, -4320), (1677, -8640), (1681, -4320), (1755, -8640), (1808, -8640), (1815, -8640), (1932, -4320), (1934, -8640), (2328, -4320), (2329, -8640), (2342, -4320), (2378, -4320), (2379, -8640), (2386, -4320), (2438, -8640), (2475, -8640), (2481, -8640), (2489, -4320), (2501, -8640), (2553, -4320), (2557, -8640), (2775, -4320), (2779, -4320), (2802, -4320), (2803, -8640)]

def row1949 : Integer.Sparse (Fin 3237) := [(822, -1), (1709, -1), (1712, -1), (1715, -1), (1755, -1), (1815, -1), (1837, -1), (1933, -1), (1948, -1), (2303, -1), (2419, -1), (2420, -1), (2423, -1), (2438, -1), (2481, -1), (2490, -1), (2491, -1), (2519, -1), (2633, -1), (2689, -1), (2716, -2), (2717, -1), (2722, -1), (2942, 4), (2943, 4), (2947, 4), (2953, 4), (3077, 4), (3078, 4), (3080, 4), (3083, 4), (3123, 4), (3125, 4), (3128, 4), (3134, 4)]

def row1950 : Integer.Sparse (Fin 3237) := [(2268, 1), (2269, 1), (2270, 1), (2277, 1), (2303, 1), (2419, 1), (2420, 1), (2422, 1), (2423, 1), (2438, 1), (2470, 1), (2471, 1), (2476, 1), (2477, 1), (2481, 1), (2490, 1), (2491, 1), (2508, 1), (2512, 1), (2513, 1), (2519, 1), (2689, 1), (2716, 1), (2717, 1)]

def row1951 : Integer.Sparse (Fin 3237) := [(1663, 1), (1664, 1), (1666, 1), (1669, 1), (1808, 1), (2633, 1), (2840, -1)]

def row1952 : Integer.Sparse (Fin 3237) := [(0, 182), (4, 10), (32, -145), (71, -160), (160, -80), (256, -80), (261, 315), (543, -4320), (544, -4320), (546, -4320), (561, -4320), (598, -4320), (1039, -4320), (1040, -4320), (1042, -4320), (1047, -4320), (1106, -4320), (1265, -4320), (1267, -4320), (1282, -4320), (1286, -4320), (1293, -4320), (1302, -4320), (1391, -4320), (1561, -4320), (1636, -4320), (1638, -4320), (1648, -4320), (1675, -4320), (1677, -4320), (1680, -4320), (1800, -4320), (1808, -8640), (1810, -4320), (1815, -4320), (1913, -4320), (1932, -4320), (1933, -4320), (2327, -4320), (2329, -4320), (2331, -4320), (2377, -4320), (2379, -4320), (2382, -4320), (2452, -4320), (2456, -4320), (2475, -8640), (2480, -4320), (2481, -4320), (2489, -4320), (2490, -4320), (2553, -4320), (2554, -4320), (2674, -4320), (2676, -4320), (2688, -4320), (2691, -4320), (2693, -4320), (2698, -4320), (2764, -4320), (2802, -4320)]

def row1953 : Integer.Sparse (Fin 3237) := [(733, -1), (1649, -1), (1753, -2), (1756, -1), (1758, -1), (1761, -1), (1932, -1), (1934, -1), (2273, -1), (2386, -1), (2437, -2), (2445, -1), (2449, -1), (2450, -1), (2489, -1), (2501, -1), (2607, -1), (2664, -1), (2682, -1), (2693, -1), (2697, -1), (2698, -1), (2942, 4), (2944, 4), (2947, 4), (2960, 4), (3068, 4), (3070, 4), (3095, 4), (3100, 4), (3101, 4), (3103, 4), (3105, 4), (3142, 4)]

def row1954 : Integer.Sparse (Fin 3237) := [(2270, 1), (2271, 1), (2273, 1), (2277, 1), (2300, 1), (2385, 1), (2386, 1), (2390, 1), (2421, 1), (2435, 1), (2436, 1), (2437, 2), (2442, 1), (2444, 1), (2445, 1), (2449, 1), (2450, 1), (2487, 1), (2489, 1), (2501, 1), (2664, 1), (2697, 1), (2698, 1)]

def row1955 : Integer.Sparse (Fin 3237) := [(1274, 1), (1275, 1), (1277, 1), (1436, 1), (2414, 1), (2828, -1)]

def row1956 : Integer.Sparse (Fin 3237) := [(730, -1), (1648, -1), (1755, -2), (1760, -2), (1780, -1), (1933, -2), (2266, -1), (2382, -1), (2430, -1), (2438, -2), (2446, -2), (2490, -2), (2606, -1), (2657, -1), (2681, -1), (2692, -1), (2693, -1), (2698, -1), (2941, 4), (2943, 8), (2959, 4), (3069, 8), (3098, 4), (3099, 8), (3108, 8), (3141, 4)]

def row1957 : Integer.Sparse (Fin 3237) := [(2265, 1), (2266, 1), (2268, 2), (2298, 1), (2382, 1), (2383, 2), (2428, 1), (2430, 1), (2432, 2), (2433, 2), (2438, 2), (2446, 2), (2483, 1), (2490, 2), (2657, 1), (2692, 1), (2693, 1)]

def row1958 : Integer.Sparse (Fin 3237) := [(732, -1), (1337, -1), (1344, -1), (1532, -1), (1543, -1), (1544, -1), (1781, -2), (1789, -2), (1908, -2), (1913, -1), (1919, -2), (1920, -1), (1949, -4), (2177, -1), (2456, -1), (2460, -1), (2573, -1), (2951, 4), (2955, 8), (2966, 4), (3075, 8), (3096, 8), (3118, 4), (3119, 8), (3184, 4)]

def row1959 : Integer.Sparse (Fin 3237) := [(1532, 1), (1543, 1), (1544, 1), (1880, 2), (1885, 2), (1886, 2), (1908, 2), (1911, 1), (1913, 1), (1917, 1), (1919, 2), (1920, 1), (1949, 2), (2134, 2), (2164, 1), (2176, 1), (2177, 1)]

def row1960 : Integer.Sparse (Fin 3237) := [(657, -1), (1163, -1), (1392, -1), (1466, -1), (1468, -2), (1567, -1), (1589, -1), (1593, -2), (1608, -2), (1618, -2), (1968, -1), (2536, -1), (2885, 4), (2890, 4), (2891, 8), (2995, 4), (2999, 4), (3000, 8), (3007, 4), (3013, 8), (3028, 8), (3048, 8), (3052, 8), (3177, 4), (3188, 4), (3197, 8)]

def row1961 : Integer.Sparse (Fin 3237) := [(1146, 1), (1160, 2), (1163, 1), (1168, 1), (1538, 1), (1539, 1), (1564, 2), (1567, 1), (1573, 2), (1589, 1), (1596, 1), (1598, 2), (1608, 2), (1613, 2), (1615, 2), (1618, 2), (1938, 1), (1955, 1), (1968, 1), (1973, 2)]

def row1962 : Integer.Sparse (Fin 3237) := [(1236, 1), (1240, 1), (1241, 2), (1471, 1), (2179, 1), (2831, -1)]

def row1963 : Integer.Sparse (Fin 3237) := [(0, 270), (3, 60), (32, 30), (66, 240), (160, -480), (218, -720), (225, -720), (260, -180), (261, 960), (434, -12960), (435, -12960), (436, -25920), (494, -12960), (495, -25920), (502, -25920), (508, -12960), (1223, -12960), (1224, -12960), (1226, -25920), (1276, -12960), (1277, -25920), (1309, -25920), (1315, -25920), (1320, -12960), (1461, -25920), (1462, -51840), (1471, -38880), (1473, -25920), (1476, -25920), (1515, -12960), (1516, -25920), (1524, -12960), (1616, -38880), (1617, -25920), (1620, -51840), (1628, -25920), (2684, -12960), (2700, -12960), (2749, -25920), (2752, -12960), (2766, -25920)]

def row1964 : Integer.Sparse (Fin 3237) := [(0, -270), (3, -60), (32, -30), (66, -240), (160, 480), (218, 720), (225, 720), (260, 180), (261, -960), (434, 12960), (435, 12960), (436, 25920), (502, 12960), (1223, 12960), (1224, 12960), (1226, 25920), (1276, 12960), (1277, 25920), (1315, 12960), (1461, 12960), (1462, 25920), (1471, 25920), (1473, 25920), (1476, 25920), (1616, 12960), (1620, 25920), (2684, 12960), (2749, 12960)]

def row1965 : Integer.Sparse (Fin 3237) := [(654, -1), (1156, -1), (1389, -1), (1466, -1), (1468, -2), (1471, -1), (1473, -1), (1477, -1), (1560, -1), (1589, -1), (1592, -1), (1608, -2), (1610, -1), (1616, -1), (1628, -1), (1629, -1), (1968, -1), (1979, -1), (2536, -1), (2538, -1), (2883, 4), (2886, 4), (2888, 4), (2891, 4), (2993, 4), (2996, 4), (2998, 4), (3000, 4), (3010, 4), (3012, 4), (3013, 4), (3047, 4), (3049, 4), (3052, 4), (3174, 4), (3193, 4), (3194, 4)]

def row1966 : Integer.Sparse (Fin 3237) := [(1139, 1), (1152, 1), (1153, 1), (1156, 1), (1160, 1), (1556, 1), (1557, 1), (1560, 1), (1564, 1), (1586, 1), (1588, 1), (1589, 1), (1604, 1), (1605, 1), (1607, 1), (1608, 2), (1610, 1), (1613, 1), (1615, 1), (1616, 1), (1628, 1), (1629, 1), (1930, 1), (1964, 1), (1967, 1), (1968, 1), (1979, 1)]

def row1967 : Integer.Sparse (Fin 3237) := [(1234, 1), (1237, 1), (1239, 1), (1241, 1), (1468, 1), (2185, 1), (2831, -1)]

def row1968 : Integer.Sparse (Fin 3237) := [(0, 327), (3, 60), (32, -30), (66, 240), (160, 480), (222, -720), (225, 240), (256, 240), (260, -180), (261, -765), (430, -12960), (431, -12960), (432, -12960), (437, -12960), (482, -12960), (483, -12960), (484, -12960), (490, -12960), (499, -12960), (509, -12960), (1217, -12960), (1219, -12960), (1222, -12960), (1227, -12960), (1274, -12960), (1275, -12960), (1278, -12960), (1300, -12960), (1301, -12960), (1305, -12960), (1312, -12960), (1321, -12960), (1415, -12960), (1416, -12960), (1417, -12960), (1424, -12960), (1438, -12960), (1440, -12960), (1443, -12960), (1466, -12960), (1467, -12960), (1468, -25920), (1470, -12960), (1477, -12960), (1509, -12960), (1510, -12960), (1511, -12960), (1525, -12960), (1569, -12960), (1589, -12960), (1590, -12960), (1593, -12960), (1608, -25920), (1609, -12960), (1611, -12960), (1618, -12960), (1619, -12960), (1629, -12960), (2682, -12960), (2697, -12960), (2729, -12960), (2742, -12960), (2753, -12960), (2768, -12960), (2769, -12960)]

def row1969 : Integer.Sparse (Fin 3237) := [(0, -327), (3, -60), (32, 30), (66, -240), (160, -480), (222, 720), (225, -240), (256, -240), (260, 180), (261, 765), (430, 12960), (431, 12960), (432, 12960), (437, 12960), (499, 12960), (1217, 12960), (1219, 12960), (1222, 12960), (1227, 12960), (1274, 12960), (1275, 12960), (1278, 12960), (1312, 12960), (1438, 12960), (1440, 12960), (1443, 12960), (1466, 12960), (1467, 12960), (1468, 25920), (1470, 12960), (1477, 12960), (1569, 12960), (1618, 12960), (1619, 12960), (2682, 12960), (2742, 12960)]

def row1970 : Integer.Sparse (Fin 3237) := [(0, 47), (4, -5), (32, 30), (71, 80), (261, -20), (649, -4320), (685, -4320), (1089, -4320), (1092, -4320), (1385, -4320), (1389, -4320), (1415, -4320), (1422, -4320), (1436, -4320), (1438, -4320), (1462, -8640), (1467, -4320), (1468, -4320), (1471, -4320), (1560, -4320), (1562, -4320), (1590, -4320), (1608, -4320), (1616, -4320), (2047, -4320), (2050, -4320), (2557, -4320), (2569, -4320), (2572, -4320), (2917, 17280), (2919, 17280), (2921, 17280), (3025, 17280), (3027, 17280), (3045, 17280), (3047, 17280), (3048, 17280), (3053, 17280), (3055, 17280), (3056, 17280), (3059, 17280), (3060, 17280), (3142, 17280), (3148, 17280)]

def row1971 : Integer.Sparse (Fin 3237) := [(653, -1), (1142, -1), (1388, -1), (1467, -2), (1470, -2), (1476, -2), (1548, -1), (1590, -2), (1592, -1), (1609, -2), (1610, -1), (1617, -2), (1969, -2), (2537, -2), (2882, 4), (2884, 4), (2887, 8), (2992, 4), (2994, 4), (2997, 8), (3009, 4), (3011, 8), (3054, 4), (3055, 8), (3169, 4), (3188, 4), (3190, 4)]

def row1972 : Integer.Sparse (Fin 3237) := [(0, -113), (3, 20), (4, -5), (32, 120), (68, 80), (160, 80), (219, -240), (255, 160), (261, 90), (879, 1440), (880, 1440), (881, 2880), (2059, 1440), (2062, 1440), (2169, 1440), (2178, 1440), (2179, 1440), (2194, 1440), (2195, 2880), (2219, 2880), (2229, 1440), (2230, 2880)]

def row1973 : Integer.Sparse (Fin 3237) := [(1136, 1), (1140, 1), (1142, 1), (1147, 2), (1547, 1), (1548, 1), (1552, 2), (1581, 1), (1582, 1), (1587, 1), (1590, 2), (1592, 1), (1597, 2), (1599, 2), (1609, 2), (1617, 2), (1923, 1), (1955, 1), (1958, 1), (1969, 2)]

def row1974 : Integer.Sparse (Fin 3237) := [(1233, 1), (1235, 1), (1238, 2), (1467, 1), (2156, 1), (2832, -1)]

def row1975 : Integer.Sparse (Fin 3237) := [(581, 1), (1233, 1), (1465, 1), (1467, 3), (2832, -1)]

def row1976 : Integer.Sparse (Fin 3237) := [(0, 192), (3, 60), (32, -60), (66, 240), (160, 960), (218, -720), (225, 480), (256, 480), (260, -180), (261, 60), (428, -12960), (429, -12960), (432, -25920), (466, -12960), (467, -12960), (474, -12960), (484, -25920), (498, -12960), (1214, -12960), (1216, -12960), (1222, -25920), (1273, -12960), (1275, -25920), (1292, -12960), (1295, -12960), (1301, -25920), (1311, -12960), (1385, -25920), (1387, -51840), (1397, -25920), (1417, -25920), (1436, -25920), (1443, -25920), (1466, -12960), (1468, -25920), (1500, -12960), (1502, -12960), (1511, -25920), (1568, -25920), (1589, -12960), (1593, -12960), (1608, -25920), (1618, -12960), (2681, -12960), (2692, -12960), (2727, -51840), (2752, -12960), (2768, -12960)]

def row1977 : Integer.Sparse (Fin 3237) := [(0, -192), (3, -60), (32, 60), (66, -240), (160, -960), (218, 720), (225, -480), (256, -480), (260, 180), (261, -60), (428, 12960), (429, 12960), (432, 25920), (498, 12960), (1214, 12960), (1216, 12960), (1222, 25920), (1273, 12960), (1275, 25920), (1311, 12960), (1387, 25920), (1436, 25920), (1443, 25920), (1466, 12960), (1468, 25920), (1568, 25920), (1618, 12960), (2681, 12960), (2727, 25920)]

def row1978 : Integer.Sparse (Fin 3237) := [(0, 38), (4, -5), (32, -5), (66, 80), (160, 80), (261, 190), (649, -8640), (1089, -8640), (1385, -8640), (1388, -4320), (1421, -4320), (1436, -8640), (1462, -17280), (1468, -8640), (1548, -4320), (1551, -4320), (1608, -8640), (2050, -4320), (2554, -4320), (2569, -4320), (2907, 17280), (2909, 17280), (2914, 17280), (3019, 17280), (3022, 17280), (3044, 34560), (3046, 34560), (3047, 17280), (3051, 34560), (3059, 17280), (3141, 17280), (3147, 34560)]

def row1979 : Integer.Sparse (Fin 3237) := [(1276, 1), (1278, 2), (1438, 1), (2416, 1), (2827, -1)]

def row1980 : Integer.Sparse (Fin 3237) := [(569, -1), (657, -1), (1120, -1), (1163, -1), (1223, -1), (1389, -2), (1392, -2), (1471, -1), (1515, -1), (1560, -2), (1567, -2), (1593, -2), (1616, -1), (1618, -2), (1932, -1), (2489, -1), (2869, 4), (2870, 8), (2979, 4), (2980, 8), (3007, 4), (3013, 8), (3021, 8), (3023, 8), (3162, 4), (3177, 4), (3179, 8)]

def row1981 : Integer.Sparse (Fin 3237) := [(1118, 2), (1120, 1), (1124, 1), (1163, 1), (1513, 2), (1515, 1), (1519, 1), (1538, 1), (1560, 2), (1564, 2), (1566, 2), (1567, 2), (1572, 2), (1616, 1), (1618, 2), (1900, 1), (1932, 1), (1938, 1), (1940, 2)]

def row1982 : Integer.Sparse (Fin 3237) := [(1206, 1), (1207, 2), (1223, 1), (1392, 1), (2358, 1), (2831, -1)]

def row1983 : Integer.Sparse (Fin 3237) := [(0, 339), (3, -60), (4, 15), (32, -120), (66, -480), (160, -960), (218, 720), (225, -240), (260, 180), (261, -690), (411, -12960), (412, -25920), (422, -12960), (450, -25920), (452, -12960), (454, -12960), (472, -12960), (497, -12960), (1184, -12960), (1185, -25920), (1194, -12960), (1252, -25920), (1254, -12960), (1256, -12960), (1340, -12960), (1342, -25920), (1385, -25920), (1392, -12960), (1394, -25920), (1397, -25920), (1415, -12960), (1424, -25920), (1436, -25920), (1438, -12960), (1466, -12960), (1536, -25920), (1541, -12960), (1567, -12960), (1568, -25920), (1569, -25920), (1577, -25920), (1589, -12960), (1593, -25920), (1618, -25920), (2609, -12960), (2667, -12960), (2726, -12960), (2741, -12960), (2758, -12960), (2765, -25920)]

def row1984 : Integer.Sparse (Fin 3237) := [(563, -1), (654, -1), (1113, -1), (1156, -1), (1217, -1), (1389, -2), (1392, -1), (1394, -1), (1398, -1), (1468, -1), (1509, -1), (1560, -2), (1567, -1), (1577, -1), (1578, -1), (1592, -1), (1608, -1), (1610, -1), (1932, -1), (1948, -1), (2489, -1), (2491, -1), (2866, 4), (2870, 4), (2976, 4), (2978, 4), (2980, 4), (3010, 4), (3012, 4), (3013, 4), (3020, 4), (3023, 4), (3159, 4), (3174, 4)]

def row1985 : Integer.Sparse (Fin 3237) := [(0, -374), (1, 100), (2, -5), (3, -200), (4, 30), (31, -300), (32, -245), (34, 80), (35, 80), (37, 320), (66, 240), (68, 480), (71, 320), (154, -240), (160, 1440), (162, 800), (165, 320), (217, -960), (219, -240), (222, -480), (224, -240), (225, 320), (251, -480), (255, 320), (256, 320), (260, -180), (261, -710), (887, 4320), (888, 4320), (1707, 4320), (1714, 4320), (1744, 4320), (2181, 4320), (2183, 4320), (2197, 4320), (2199, 4320), (2218, 4320), (2220, 4320), (2237, 4320)]

def row1986 : Integer.Sparse (Fin 3237) := [(1111, 1), (1113, 1), (1118, 1), (1156, 1), (1506, 1), (1507, 1), (1509, 1), (1513, 1), (1556, 1), (1557, 1), (1559, 1), (1560, 2), (1564, 1), (1566, 1), (1567, 1), (1577, 1), (1578, 1), (1608, 1), (1610, 1), (1893, 1), (1930, 1), (1932, 1), (1948, 1)]

def row1987 : Integer.Sparse (Fin 3237) := [(1203, 1), (1205, 1), (1207, 1), (1217, 1), (1389, 1), (2356, 1), (2831, -1)]

def row1988 : Integer.Sparse (Fin 3237) := [(0, 369), (3, -60), (4, 15), (32, -195), (66, -240), (71, -240), (160, -1200), (222, 720), (225, -480), (256, -720), (260, 180), (261, 105), (408, -12960), (409, -12960), (413, -12960), (419, -12960), (444, -12960), (445, -12960), (447, -12960), (455, -12960), (469, -12960), (486, -12960), (1182, -12960), (1183, -12960), (1186, -12960), (1191, -12960), (1247, -12960), (1248, -12960), (1249, -12960), (1257, -12960), (1337, -12960), (1339, -12960), (1343, -12960), (1359, -12960), (1361, -12960), (1367, -12960), (1368, -12960), (1370, -25920), (1388, -12960), (1389, -25920), (1391, -12960), (1398, -12960), (1420, -25920), (1422, -12960), (1532, -12960), (1533, -12960), (1542, -12960), (1548, -12960), (1549, -25920), (1560, -25920), (1561, -12960), (1562, -12960), (1578, -12960), (1591, -25920), (1592, -12960), (1610, -12960), (2607, -12960), (2664, -12960), (2717, -12960), (2722, -12960), (2757, -12960), (2762, -12960), (2764, -12960)]

def row1989 : Integer.Sparse (Fin 3237) := [(0, 47), (4, -5), (32, 30), (71, 80), (261, -20), (598, -4320), (617, -4320), (1047, -4320), (1049, -4320), (1303, -8640), (1305, -4320), (1312, -4320), (1385, -4320), (1388, -4320), (1389, -4320), (1392, -4320), (1422, -4320), (1436, -4320), (1468, -4320), (1548, -4320), (1560, -4320), (1562, -4320), (1567, -4320), (1608, -4320), (1753, -4320), (2081, -4320), (2437, -4320), (2555, -4320), (2557, -4320), (2897, 17280), (2917, 17280), (3025, 17280), (3026, 17280), (3030, 17280), (3031, 17280), (3032, 17280), (3045, 17280), (3047, 17280), (3048, 17280), (3129, 17280)]

def row1990 : Integer.Sparse (Fin 3237) := [(561, -1), (653, -1), (1106, -1), (1142, -1), (1214, -1), (1391, -2), (1397, -2), (1420, -1), (1467, -1), (1500, -1), (1549, -1), (1561, -2), (1568, -2), (1590, -1), (1592, -1), (1610, -1), (1933, -2), (2490, -2), (2867, 8), (2975, 4), (2977, 8), (3009, 4), (3011, 8), (3026, 8), (3155, 4), (3169, 4)]

def row1991 : Integer.Sparse (Fin 3237) := [(0, -420), (1, 100), (2, -5), (3, 260), (4, -65), (31, -300), (32, 475), (34, 160), (35, 160), (37, 160), (154, -480), (160, 160), (162, 160), (165, 320), (215, -240), (217, -480), (218, -240), (219, 480), (224, -480), (225, 160), (255, -320), (260, -180), (261, 555), (889, 8640), (2056, 4320), (2059, 4320), (2169, 4320), (2172, 4320), (2198, 8640), (2219, 8640), (2238, 8640)]

def row1992 : Integer.Sparse (Fin 3237) := [(1106, 1), (1108, 2), (1142, 1), (1499, 1), (1500, 1), (1503, 2), (1547, 1), (1549, 1), (1552, 2), (1553, 2), (1561, 2), (1568, 2), (1590, 1), (1592, 1), (1888, 1), (1923, 1), (1933, 2)]

def row1993 : Integer.Sparse (Fin 3237) := [(0, 216), (3, -60), (4, 15), (32, -75), (66, -480), (160, -1680), (218, 720), (225, -960), (256, -480), (260, 180), (261, 930), (407, -12960), (409, -25920), (418, -12960), (442, -12960), (443, -12960), (445, -25920), (468, -25920), (1181, -12960), (1183, -25920), (1190, -12960), (1245, -12960), (1246, -12960), (1248, -25920), (1336, -12960), (1339, -25920), (1358, -51840), (1361, -51840), (1368, -51840), (1388, -38880), (1389, -25920), (1420, -12960), (1529, -12960), (1533, -25920), (1548, -38880), (1549, -12960), (1560, -25920), (1591, -25920), (2606, -12960), (2657, -12960), (2716, -51840), (2756, -12960), (2762, -12960)]

def row1994 : Integer.Sparse (Fin 3237) := [(0, 38), (4, -5), (32, -5), (66, 80), (160, 80), (261, 190), (598, -8640), (1047, -8640), (1293, -4320), (1295, -4320), (1302, -4320), (1311, -4320), (1385, -8640), (1389, -8640), (1421, -4320), (1436, -8640), (1467, -4320), (1551, -4320), (1560, -8640), (1590, -4320), (1752, -4320), (2429, -4320), (2554, -4320), (2896, 17280), (2907, 17280), (3024, 34560), (3029, 34560), (3031, 17280), (3044, 34560), (3047, 17280), (3128, 34560)]

def row1995 : Integer.Sparse (Fin 3237) := [(572, -1), (695, -1), (1121, -1), (1165, -1), (1226, -1), (1342, -1), (1397, -1), (1420, -1), (1422, -1), (1424, -1), (1516, -1), (1536, -1), (1549, -1), (1562, -1), (1568, -1), (1569, -1), (1611, -1), (1619, -1), (1620, -2), (1934, -1), (2501, -1), (2875, 4), (2878, 4), (2879, 4), (2986, 4), (2989, 4), (2990, 4), (3007, 4), (3008, 4), (3026, 4), (3028, 4), (3032, 4), (3034, 4), (3035, 4), (3164, 4), (3168, 4), (3180, 4), (3181, 4)]

def row1996 : Integer.Sparse (Fin 3237) := [(1109, 1), (1121, 1), (1122, 1), (1126, 1), (1165, 1), (1504, 1), (1516, 1), (1517, 1), (1521, 1), (1536, 1), (1537, 1), (1538, 1), (1549, 1), (1553, 1), (1554, 1), (1562, 1), (1568, 1), (1569, 1), (1570, 1), (1573, 1), (1574, 1), (1619, 1), (1620, 1), (1902, 1), (1915, 1), (1934, 1), (1941, 1), (1942, 1)]

def row1997 : Integer.Sparse (Fin 3237) := [(1218, 1), (1225, 1), (1226, 1), (1228, 1), (1424, 1), (2374, 1), (2832, -1)]

def row1998 : Integer.Sparse (Fin 3237) := [(0, 37), (4, -5), (32, 50), (66, 80), (160, 160), (261, -70), (622, -4320), (1069, -4320), (1305, -4320), (1312, -4320), (1316, -4320), (1319, -4320), (1329, -4320), (1330, -4320), (1370, -8640), (1392, -4320), (1422, -4320), (1424, -4320), (1471, -4320), (1562, -4320), (1567, -4320), (1569, -4320), (1616, -4320), (1784, -4320), (2097, -4320), (2447, -4320), (2556, -4320), (2562, -4320), (2900, 17280), (2901, 17280), (2902, 17280), (2925, 17280), (3017, 17280), (3018, 17280), (3026, 17280), (3027, 17280), (3030, 17280), (3040, 17280), (3041, 17280), (3042, 17280), (3055, 17280), (3056, 17280), (3125, 17280), (3137, 17280)]

def row1999 : Integer.Sparse (Fin 3237) := [(567, -1), (693, -1), (1115, -1), (1158, -1), (1222, -1), (1339, -1), (1420, -1), (1422, -2), (1424, -1), (1426, -1), (1511, -1), (1533, -1), (1549, -1), (1562, -2), (1569, -1), (1580, -1), (1611, -1), (1619, -1), (1934, -1), (1950, -1), (2501, -1), (2503, -1), (2876, 4), (2879, 4), (2985, 4), (2987, 4), (2990, 4), (3005, 4), (3008, 4), (3031, 4), (3033, 4), (3035, 4), (3160, 4), (3175, 4)]

def row2000 : Integer.Sparse (Fin 3237) := [(1115, 1), (1116, 1), (1122, 1), (1158, 1), (1501, 1), (1511, 1), (1512, 1), (1517, 1), (1533, 1), (1534, 1), (1537, 1), (1549, 1), (1550, 1), (1562, 2), (1563, 1), (1569, 1), (1570, 1), (1580, 1), (1611, 1), (1897, 1), (1934, 1), (1935, 1), (1950, 1)]

def row2001 : Integer.Sparse (Fin 3237) := [(1215, 1), (1220, 1), (1222, 1), (1228, 1), (1422, 1), (2371, 1), (2832, -1)]

def row2002 : Integer.Sparse (Fin 3237) := [(0, 81), (32, 20), (160, 160), (225, 80), (256, 80), (261, 155), (419, -4320), (420, -4320), (421, -4320), (425, -4320), (447, -4320), (448, -4320), (449, -4320), (461, -4320), (488, -8640), (1191, -4320), (1192, -4320), (1193, -4320), (1197, -4320), (1249, -4320), (1250, -4320), (1251, -4320), (1262, -4320), (1267, -4320), (1268, -4320), (1271, -4320), (1281, -4320), (1282, -4320), (1289, -4320), (1303, -8640), (1370, -8640), (1373, -8640), (1376, -8640), (1389, -4320), (1391, -4320), (1398, -4320), (1420, -4320), (1421, -4320), (1422, -8640), (1549, -4320), (1551, -4320), (1560, -4320), (1561, -4320), (1562, -8640), (1578, -4320), (1592, -8640), (1610, -8640), (2621, -4320), (2665, -4320), (2676, -4320), (2688, -4320), (2723, -8640), (2763, -4320), (2764, -4320)]

def row2003 : Integer.Sparse (Fin 3237) := [(0, 47), (4, -5), (32, 30), (71, 80), (261, -20), (605, -4320), (622, -4320), (1066, -4320), (1069, -4320), (1303, -8640), (1306, -4320), (1328, -4320), (1361, -4320), (1368, -4320), (1370, -8640), (1389, -4320), (1417, -4320), (1424, -4320), (1443, -4320), (1468, -4320), (1560, -4320), (1569, -4320), (1608, -4320), (1782, -4320), (2097, -4320), (2439, -4320), (2556, -4320), (2557, -4320), (2898, 17280), (2919, 17280), (3016, 17280), (3025, 34560), (3026, 17280), (3038, 17280), (3040, 17280), (3053, 17280), (3055, 17280), (3136, 17280)]

def row2004 : Integer.Sparse (Fin 3237) := [(563, -1), (570, -1), (573, -2), (1113, -1), (1130, -1), (1131, -2), (1217, -1), (1224, -1), (1227, -2), (1340, -1), (1343, -2), (1389, -2), (1394, -2), (1398, -2), (1509, -1), (1524, -1), (1525, -2), (1541, -1), (1542, -2), (1560, -2), (1577, -2), (1578, -2), (1907, -1), (1918, -1), (1948, -2), (2373, -1), (2458, -1), (2491, -2), (2831, 4)]

def row2005 : Integer.Sparse (Fin 3237) := [(561, -1), (565, -1), (567, -1), (572, -1), (1106, -1), (1114, -1), (1115, -1), (1121, -1), (1214, -1), (1219, -1), (1222, -1), (1226, -1), (1337, -1), (1339, -1), (1342, -1), (1388, -1), (1391, -1), (1397, -1), (1420, -1), (1422, -1), (1424, -1), (1500, -1), (1510, -1), (1511, -1), (1516, -1), (1532, -1), (1533, -1), (1536, -1), (1548, -1), (1549, -1), (1561, -1), (1562, -1), (1568, -1), (1569, -1), (1896, -1), (1913, -1), (1933, -1), (1934, -1), (2370, -1), (2456, -1), (2490, -1), (2501, -1), (2832, 4)]

def row2006 : Integer.Sparse (Fin 3237) := [(562, -1), (692, -1), (1107, -1), (1145, -1), (1216, -1), (1336, -1), (1421, -3), (1429, -2), (1502, -1), (1529, -1), (1551, -3), (1571, -2), (1595, -1), (1631, -1), (1936, -2), (2502, -2), (2877, 8), (2984, 4), (2988, 8), (3006, 8), (3039, 4), (3040, 8), (3157, 4), (3171, 4)]

def row2007 : Integer.Sparse (Fin 3237) := [(1107, 1), (1110, 2), (1145, 1), (1498, 1), (1502, 1), (1505, 2), (1529, 1), (1530, 2), (1546, 1), (1551, 3), (1555, 2), (1571, 2), (1595, 1), (1890, 1), (1925, 1), (1936, 2)]

def row2008 : Integer.Sparse (Fin 3237) := [(1213, 1), (1216, 1), (1221, 2), (1421, 1), (2368, 1), (2833, -1)]

def row2009 : Integer.Sparse (Fin 3237) := [(1213, 1), (1419, 1), (1421, 3), (2833, -1)]

def row2010 : Integer.Sparse (Fin 3237) := [(545, -1), (546, -2), (558, -1), (1041, -1), (1042, -2), (1076, -1), (1200, -1), (1201, -2), (1211, -1), (1356, -1), (1357, -2), (1359, -2), (1361, -2), (1367, -2), (1368, -2), (1370, -4), (1385, -2), (1415, -1), (1430, -1), (1436, -2), (1438, -1), (1796, -1), (1808, -2), (1810, -1), (2351, -1), (2475, -2), (2480, -1), (2828, 4)]

def row2011 : Integer.Sparse (Fin 3237) := [(534, -2), (537, -1), (617, -1), (1023, -2), (1028, -1), (1049, -1), (1191, -2), (1194, -1), (1249, -2), (1254, -1), (1303, -4), (1305, -4), (1312, -4), (1315, -2), (1389, -2), (1392, -1), (1560, -2), (1567, -1), (1681, -1), (1753, -2), (1756, -1), (2342, -1), (2437, -2), (2445, -1), (2828, 4)]

def row2012 : Integer.Sparse (Fin 3237) := [(2811, 1), (2812, 1), (2813, 2), (2817, 1), (2821, 1), (2822, 1), (2823, 2), (2825, 1), (2826, 2), (2827, 1), (2828, 5), (2829, 2), (2830, 2), (2831, 1), (2832, 2), (2836, 1), (2838, 1), (2839, 1), (2840, 2)]

def row2013 : Integer.Sparse (Fin 3237) := [(2192, 3), (2194, 1), (2211, 1), (2369, 1), (2831, -1)]

def row2014 : Integer.Sparse (Fin 3237) := [(0, 489), (3, -60), (4, -45), (32, 280), (71, 480), (160, -640), (218, 240), (222, 480), (225, -480), (256, -640), (260, 180), (261, -140), (730, -8640), (733, -8640), (1992, -8640), (1993, -8640), (2081, -17280), (2266, -8640), (2273, -8640), (2317, -4320), (2542, -8640), (2545, -8640), (2555, -17280), (2557, -17280), (2562, -8640), (2570, -8640), (2751, -4320), (2762, -8640)]

def row2015 : Integer.Sparse (Fin 3237) := [(0, 504), (3, -60), (4, -30), (32, 110), (66, 160), (71, 80), (160, 160), (222, 240), (256, -320), (260, 180), (261, 740), (273, 480), (561, -8640), (563, -8640), (652, -4320), (1106, -8640), (1113, -8640), (1141, -4320), (1648, -8640), (1649, -8640), (1808, -17280), (1810, -8640), (1932, -8640), (2382, -8640), (2386, -8640), (2475, -17280), (2480, -8640), (2489, -8640), (2554, -8640), (2557, -17280), (2570, -8640), (2798, -4320), (2802, -8640)]

def row2016 : Integer.Sparse (Fin 3237) := [(865, -1), (1810, -3), (1968, -3), (2314, -1), (2480, -3), (2536, -3), (2642, -1), (2726, -3), (2733, -1), (2741, -3), (2951, 4), (2952, 12), (3084, 12), (3087, 4), (3129, 24), (3132, 12)]

def row2017 : Integer.Sparse (Fin 3237) := [(1911, 1), (1912, 1), (1916, 3), (2267, 3), (2314, 1), (2480, 3), (2509, 3), (2517, 6), (2536, 3), (2733, 1), (2741, 3)]

def row2018 : Integer.Sparse (Fin 3237) := [(0, 86), (4, -5), (32, 45), (66, 80), (160, 240), (256, 160), (261, -120), (558, -4320), (569, -1440), (648, -1440), (1076, -4320), (1088, -1440), (1120, -1440), (1646, -4320), (1654, -1440), (1796, -4320), (1837, -8640), (1895, -1440), (1968, -4320), (2351, -4320), (2369, -1440), (2380, -4320), (2392, -1440), (2519, -8640), (2536, -4320), (2562, -4320), (2767, -1440), (2794, -4320), (2797, -1440)]

def row2019 : Integer.Sparse (Fin 3237) := [(652, -1), (1141, -1), (1468, -4), (1471, -2), (1591, -4), (1608, -4), (1616, -2), (1968, -2), (2536, -2), (2883, 8), (2885, 8), (2993, 8), (2995, 8), (3047, 8), (3048, 16), (3187, 4), (3189, 8)]

def row2020 : Integer.Sparse (Fin 3237) := [(1139, 2), (1141, 1), (1146, 2), (1586, 2), (1588, 2), (1591, 2), (1596, 2), (1598, 4), (1608, 4), (1616, 2), (1954, 1), (1957, 2), (1968, 2)]

def row2021 : Integer.Sparse (Fin 3237) := [(0, 106), (3, -60), (32, 20), (66, -240), (160, -320), (218, 240), (222, 480), (260, 180), (261, -190), (428, -8640), (430, -8640), (466, -8640), (472, -4320), (482, -8640), (497, -4320), (1214, -8640), (1217, -8640), (1385, -17280), (1392, -8640), (1415, -8640), (1436, -17280), (1438, -8640), (1467, -8640), (1468, -17280), (1500, -8640), (1509, -8640), (1567, -8640), (1590, -8640), (1593, -8640), (1608, -17280), (1618, -8640), (2726, -8640), (2741, -8640), (2751, -4320), (2768, -8640)]

def row2022 : Integer.Sparse (Fin 3237) := [(0, 49), (4, 15), (32, -110), (66, -80), (71, -160), (160, -160), (261, -70), (648, -8640), (1088, -8640), (1420, -8640), (1461, -17280), (1466, -17280), (1549, -8640), (1589, -17280), (2046, -8640), (2553, -4320), (2566, -8640), (2908, 34560), (2912, 17280), (3045, 69120), (3050, 34560), (3054, 34560), (3058, 34560), (3146, 34560)]

def row2023 : Integer.Sparse (Fin 3237) := [(561, -1), (691, -1), (1106, -1), (1143, -1), (1214, -1), (1388, -1), (1422, -2), (1424, -2), (1500, -1), (1548, -1), (1562, -2), (1569, -2), (1592, -1), (1593, -1), (1610, -1), (1618, -1), (1934, -2), (2501, -2), (2875, 8), (2985, 4), (2986, 8), (3026, 8), (3031, 4), (3032, 8), (3156, 4), (3170, 4)]

def row2024 : Integer.Sparse (Fin 3237) := [(1106, 1), (1109, 2), (1143, 1), (1500, 1), (1501, 1), (1504, 2), (1548, 1), (1550, 1), (1553, 2), (1554, 2), (1562, 2), (1569, 2), (1592, 1), (1593, 1), (1889, 1), (1924, 1), (1934, 2)]

def row2025 : Integer.Sparse (Fin 3237) := [(2811, 4), (2816, 1), (2821, 4), (2828, 12), (2831, 4), (2835, 1), (2839, 4)]

def row2026 : Integer.Sparse (Fin 3237) := [(1226, 1), (2195, 1), (2349, 1), (2359, 1), (2370, 1), (2374, 1), (2832, -1)]

def row2027 : Integer.Sparse (Fin 3237) := [(1674, 1), (2140, 1), (2141, 1), (2148, 1), (2153, 1), (2643, 1), (2840, -1)]

def row2028 : Integer.Sparse (Fin 3237) := [(1659, 1), (2003, 1), (2592, 1), (2616, 1), (2621, 1), (2622, 1), (2840, -1)]

def row2029 : Integer.Sparse (Fin 3237) := [(1642, 1), (1987, 1), (2595, 1), (2602, 1), (2607, 1), (2609, 1), (2839, -1)]

def row2030 : Integer.Sparse (Fin 3237) := [(1666, 1), (2198, 1), (2623, 1), (2629, 1), (2633, 1), (2636, 1), (2840, -1)]

def row2031 : Integer.Sparse (Fin 3237) := [(2007, 2), (2624, 1), (2630, 1), (2674, 1), (2770, 1), (2839, -1)]

def row2032 : Integer.Sparse (Fin 3237) := [(1667, 1), (2199, 1), (2624, 1), (2630, 1), (2635, 2), (2839, -1)]

def row2033 : Integer.Sparse (Fin 3237) := [(0, 180), (218, -720), (260, -180), (261, 720), (1226, -12960), (1229, -3240), (1231, -6480), (1476, -6480), (1516, -12960), (1518, -3240), (1528, -6480), (1617, -6480), (2001, -12960), (2004, -3240), (2546, -12960), (2549, -3240), (2563, -6480), (2623, -6480), (2643, -12960), (2686, -6480), (2701, -12960), (2750, -6480), (2752, -12960), (2766, -6480)]

def row2034 : Integer.Sparse (Fin 3237) := [(0, -180), (218, 720), (260, 180), (261, -720), (1226, 12960), (1229, 3240), (1231, 6480), (1476, 6480), (2001, 12960), (2004, 3240), (2623, 6480), (2643, 12960), (2750, 3240)]

def row2035 : Integer.Sparse (Fin 3237) := [(0, 27), (222, 360), (260, 90), (261, -45), (1909, -6480), (2376, -6480), (2610, -12960), (2668, -12960), (2755, -3240), (3163, 51840), (3165, 12960), (3196, 12960), (3213, 12960)]

def row2036 : Integer.Sparse (Fin 3237) := [(0, 108), (222, -360), (260, -90), (261, -90), (1227, -2160), (1230, -2160), (1477, -1080), (1525, -2160), (1527, -2160), (1629, -1080), (1657, -4320), (1661, -2160), (2002, -2160), (2393, -4320), (2399, -2160), (2547, -2160), (2563, -2160), (2565, -1080), (2624, -2160), (2685, -2160), (2687, -2160), (2705, -2160), (2753, -4320), (2759, -2160), (2769, -2160)]

def row2037 : Integer.Sparse (Fin 3237) := [(0, -108), (222, 360), (260, 90), (261, 90), (1227, 2160), (1230, 2160), (1477, 1080), (1657, 4320), (1661, 2160), (2002, 2160), (2624, 2160), (2685, 2160)]

def row2038 : Integer.Sparse (Fin 3237) := [(0, 20), (218, 192), (260, 72), (261, 100), (273, 96), (1909, -3456), (2376, -3456), (2610, -6912), (2611, -3456), (2668, -6912), (2671, -3456), (2754, -1728), (2800, -864), (3166, 13824), (3199, 3456), (3214, 6912)]

def row2039 : Integer.Sparse (Fin 3237) := [(1657, -1), (1760, -1), (1815, -1), (2001, -1), (2393, -1), (2446, -1), (2481, -1), (2546, -1), (2590, -1), (2606, -1), (2622, -1), (2633, -1), (2643, -1), (2654, -1), (2657, -1), (2669, -1), (2689, -1), (2699, -1), (2701, -1), (2703, -1), (2723, -2), (2980, 4), (2981, 4), (2982, 4), (2990, 4), (3052, 4), (3069, 4), (3071, 4), (3078, 4), (3080, 4), (3082, 4), (3086, 4), (3144, 4), (3202, 4), (3206, 4), (3215, 4), (3218, 4), (3232, 4)]

def row2040 : Integer.Sparse (Fin 3237) := [(0, -630), (32, -270), (218, -1440), (222, -1440), (224, -1440), (260, 1080), (261, 360), (1207, 8640), (1208, 8640), (1209, 8640), (1228, 8640), (1455, 8640), (1666, 8640), (1668, 8640), (1857, 8640), (1987, 8640), (1988, 8640), (2003, 8640), (2007, 8640), (2625, 8640), (2638, 8640), (2644, 8640), (2678, 8640), (2747, 8640)]

def row2041 : Integer.Sparse (Fin 3237) := [(1513, 1), (1514, 1), (1517, 1), (1523, 1), (1615, 1), (2383, 1), (2391, 1), (2393, 1), (2446, 1), (2470, 1), (2471, 1), (2474, 1), (2481, 1), (2495, 1), (2510, 1), (2546, 1), (2654, 1), (2657, 1), (2660, 1), (2661, 1), (2669, 1), (2689, 1), (2701, 1), (2703, 1), (2711, 1), (2723, 1), (2734, 1), (2748, 1)]

def row2042 : Integer.Sparse (Fin 3237) := [(1664, 1), (2197, 1), (2590, 1), (2610, 1), (2633, 1), (2634, 1), (2840, -1)]

def row2043 : Integer.Sparse (Fin 3237) := [(1640, 1), (1984, 1), (2593, 1), (2606, 1), (2608, 1), (2610, 1), (2840, -1)]

def row2044 : Integer.Sparse (Fin 3237) := [(1672, 1), (2202, 1), (2593, 1), (2610, 1), (2643, 1), (2644, 1), (2840, -1)]

def row2045 : Integer.Sparse (Fin 3237) := [(1222, -2), (1230, -1), (1231, -1), (1511, -2), (1527, -1), (1528, -1), (1789, -1), (1896, -2), (1908, -1), (1920, -2), (1950, -1), (2160, -1), (2370, -2), (2460, -2), (2503, -1), (2574, -1), (3000, 8), (3001, 4), (3002, 4), (3062, 4), (3075, 8), (3088, 8), (3151, 4), (3152, 8), (3160, 8), (3192, 8), (3198, 4)]

def row2046 : Integer.Sparse (Fin 3237) := [(0, -114), (32, 150), (224, 480), (260, 120), (261, 120), (1241, 2880), (1242, 1440), (1243, 1440), (1497, 1440), (1674, 2880), (1874, 1440), (1962, 2880), (1974, 1440), (2010, 2880), (2180, 2880), (2184, 2880)]

def row2047 : Integer.Sparse (Fin 3237) := [(1511, 2), (1527, 1), (1528, 1), (1613, 2), (1614, 1), (1621, 1), (1627, 1), (1881, 2), (1886, 2), (1887, 2), (1896, 2), (1897, 2), (1908, 1), (1910, 1), (1920, 2), (1950, 1), (2135, 2), (2160, 1), (2161, 1)]

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

def row2048 : Integer.Sparse (Fin 3237) := [(0, 528), (260, -360), (261, 120), (273, -1440), (1658, -25920), (1660, -12960), (2397, -25920), (2398, -12960), (2565, -12960), (2799, -25920)]

def row2049 : Integer.Sparse (Fin 3237) := [(0, -528), (260, 360), (261, -120), (273, 1440), (1658, 25920), (1660, 12960)]

def row2050 : Integer.Sparse (Fin 3237) := [(0, 27), (222, 360), (260, 90), (261, -45), (2611, -12960), (2671, -12960), (2755, -3240)]

def row2051 : Integer.Sparse (Fin 3237) := [(1658, -1), (1761, -1), (2002, -1), (2087, -2), (2397, -1), (2450, -1), (2547, -1), (2561, -2), (2591, -1), (2607, -2), (2656, -1), (2664, -2), (2674, -1), (2685, -1), (2691, -1), (2705, -1), (2783, -2), (2786, -2), (3070, 8), (3071, 8), (3072, 8), (3076, 8), (3081, 4), (3145, 4), (3203, 4), (3234, 4)]

def row2052 : Integer.Sparse (Fin 3237) := [(2390, 2), (2391, 2), (2394, 2), (2395, 2), (2397, 1), (2450, 1), (2473, 1), (2499, 1), (2547, 1), (2561, 2), (2656, 1), (2663, 1), (2664, 2), (2691, 1), (2705, 1), (2785, 1), (2786, 2)]

def row2053 : Integer.Sparse (Fin 3237) := [(2006, 2), (2591, 1), (2611, 1), (2674, 1), (2839, -1)]

def row2054 : Integer.Sparse (Fin 3237) := [(1985, 1), (2594, 1), (2607, 2), (2611, 1), (2839, -1)]

def row2055 : Integer.Sparse (Fin 3237) := [(2009, 2), (2594, 1), (2611, 1), (2685, 1), (2772, 1), (2839, -1)]

def row2056 : Integer.Sparse (Fin 3237) := [(1653, -4), (1660, -1), (1661, -2), (1997, -4), (2004, -1), (2055, -2), (2388, -4), (2398, -1), (2399, -2), (2548, -4), (2549, -1), (2577, -2), (2589, -2), (2621, -4), (2653, -2), (2665, -4), (2787, -2), (2840, 4)]

def row2057 : Integer.Sparse (Fin 3237) := [(2388, 4), (2398, 1), (2399, 2), (2548, 4), (2549, 1), (2577, 2), (2653, 2), (2665, 4), (2787, 1), (2840, 1)]

def row2058 : Integer.Sparse (Fin 3237) := [(2823, 8), (2824, 4), (2830, 4), (2834, 2), (2836, 8), (2840, 4)]

def row2059 : Integer.Sparse (Fin 3237) := [(0, 342), (3, -60), (32, 30), (66, -240), (160, -480), (218, 720), (225, -240), (260, 180), (261, 1800), (1223, -4320), (1224, -4320), (1226, -8640), (1471, -4320), (1515, -4320), (1516, -8640), (1524, -4320), (1616, -4320), (1998, -4320), (1999, -4320), (2001, -8640), (2060, -4320), (2540, -4320), (2543, -4320), (2546, -8640), (2550, -4320), (2554, -4320), (2563, -8640), (2623, -8640), (2642, -4320), (2643, -8640), (2684, -4320), (2686, -8640), (2700, -4320), (2701, -8640), (2733, -4320), (2749, -8640), (2752, -8640), (2754, -8640), (2756, -4320), (2763, -4320), (2766, -8640)]

def row2060 : Integer.Sparse (Fin 3237) := [(0, 90), (3, -12), (32, 6), (66, -48), (160, -96), (218, 144), (225, -48), (260, 36), (261, -180), (1214, -1296), (1216, -1296), (1222, -2592), (1342, -1296), (1345, -1296), (1397, -2592), (1467, -1296), (1500, -1296), (1502, -1296), (1511, -2592), (1536, -1296), (1545, -1296), (1568, -2592), (1590, -1296), (1992, -1296), (1997, -2592), (2545, -1296), (2548, -2592), (2562, -1296), (2590, -2592), (2610, -2592), (2633, -2592), (2654, -2592), (2668, -2592), (2681, -1296), (2689, -2592), (2692, -1296), (2727, -5184), (2751, -1296), (2753, -2592), (2758, -1296), (2765, -2592), (2768, -1296)]

def row2061 : Integer.Sparse (Fin 3237) := [(0, 63), (3, 30), (32, -10), (66, 80), (71, 40), (160, 160), (222, -360), (256, 80), (260, -90), (261, -125), (1896, -4320), (1907, -2160), (1920, -2160), (2370, -4320), (2373, -2160), (2460, -2160), (2606, -2160), (2609, -2160), (2622, -4320), (2633, -4320), (2635, -2160), (2643, -4320), (2657, -2160), (2667, -2160), (2669, -4320), (2689, -4320), (2701, -4320), (2715, -2160), (2753, -4320), (2759, -2160), (3155, 8640), (3157, 8640), (3162, 8640), (3164, 17280), (3167, 8640), (3178, 17280), (3188, 8640), (3216, 17280)]

def row2062 : Integer.Sparse (Fin 3237) := [(0, 423), (3, -60), (32, 30), (66, -240), (160, -480), (222, 720), (256, -240), (260, 180), (261, -225), (1217, -4320), (1219, -4320), (1222, -4320), (1227, -4320), (1468, -4320), (1509, -4320), (1510, -4320), (1511, -4320), (1525, -4320), (1608, -4320), (1715, -4320), (1718, -4320), (1760, -4320), (1993, -4320), (1997, -4320), (2002, -4320), (2423, -4320), (2427, -4320), (2446, -4320), (2542, -4320), (2547, -4320), (2548, -4320), (2557, -4320), (2563, -4320), (2590, -4320), (2610, -4320), (2624, -4320), (2635, -4320), (2654, -4320), (2668, -4320), (2682, -4320), (2687, -4320), (2697, -4320), (2715, -4320), (2729, -4320), (2742, -4320), (2751, -4320), (2752, -4320), (2753, -8640), (2755, -4320), (2757, -4320), (2764, -4320), (2768, -4320), (2769, -4320)]

def row2063 : Integer.Sparse (Fin 3237) := [(0, 978), (3, 480), (32, -180), (66, 1440), (71, 480), (160, 2880), (218, -2880), (222, -1440), (225, 960), (256, 480), (260, -1440), (261, 1050), (273, -1440), (1896, -51840), (1907, -51840), (2370, -51840), (2373, -51840), (2607, -51840), (2621, -51840), (2633, -51840), (2635, -51840), (2643, -51840), (2664, -51840), (2665, -51840), (2689, -51840), (2701, -51840), (2715, -51840), (2752, -51840), (2753, -25920), (2799, -25920), (3159, 207360), (3160, 207360), (3193, 103680), (3215, 207360), (3218, 103680)]

def row2064 : Integer.Sparse (Fin 3237) := [(1760, -1), (1837, -1), (2446, -1), (2519, -1), (2610, -1), (2633, -1), (2668, -1), (2681, -1), (2689, -1), (2692, -1), (2699, -1), (2703, -1), (2727, -2), (2729, -1), (2742, -1), (2986, 4), (2987, 4), (2988, 4), (2990, 4), (3055, 4), (3083, 4), (3085, 4), (3086, 4), (3088, 4), (3099, 4), (3144, 4), (3153, 4), (3163, 4), (3178, 4), (3202, 4), (3216, 4), (3217, 4), (3218, 4), (3220, 4), (3230, 4), (3232, 4)]

def row2065 : Integer.Sparse (Fin 3237) := [(1504, 1), (1505, 1), (1512, 1), (1517, 1), (1599, 1), (1882, 1), (1887, 1), (1901, 1), (1939, 1), (2432, 1), (2443, 1), (2446, 1), (2495, 1), (2508, 1), (2510, 1), (2519, 1), (2660, 1), (2668, 1), (2689, 1), (2692, 1), (2695, 1), (2703, 1), (2713, 1), (2727, 1), (2728, 1), (2732, 1), (2734, 1), (2742, 1), (2747, 1)]

def row2066 : Integer.Sparse (Fin 3237) := [(0, 723), (3, -60), (32, 75), (66, -240), (160, -1200), (218, 720), (225, -960), (256, -480), (260, 180), (261, -540), (1200, -12960), (1201, -25920), (1217, -12960), (1356, -12960), (1357, -25920), (1415, -12960), (1438, -12960), (1509, -12960), (1704, -12960), (1705, -12960), (1760, -25920), (1982, -25920), (1993, -12960), (2400, -12960), (2401, -12960), (2446, -25920), (2542, -12960), (2544, -25920), (2588, -25920), (2596, -25920), (2610, -25920), (2618, -12960), (2633, -25920), (2651, -12960), (2668, -25920), (2689, -25920), (2726, -12960), (2729, -25920), (2741, -12960), (2742, -25920), (2751, -12960), (2753, -25920), (2761, -12960), (2762, -12960), (2764, -25920), (2788, -12960)]

def row2067 : Integer.Sparse (Fin 3237) := [(1810, -1), (2060, -1), (2480, -1), (2550, -1), (2624, -2), (2635, -2), (2642, -1), (2687, -2), (2715, -2), (2717, -2), (2722, -2), (2733, -1), (2761, -1), (2767, -1), (2788, -1), (2797, -1), (2975, 4), (2978, 8), (2985, 4), (3047, 4), (3079, 4), (3081, 8), (3084, 4), (3123, 8), (3214, 8), (3215, 8), (3229, 8)]

def row2068 : Integer.Sparse (Fin 3237) := [(1499, 1), (1501, 1), (1507, 2), (1588, 1), (2472, 1), (2473, 2), (2476, 2), (2480, 1), (2509, 1), (2550, 1), (2687, 2), (2711, 2), (2714, 2), (2715, 2), (2722, 2), (2725, 2), (2733, 1), (2761, 1), (2767, 1)]

def row2069 : Integer.Sparse (Fin 3237) := [(1715, -1), (1760, -1), (1808, -1), (2423, -1), (2446, -1), (2475, -1), (2590, -1), (2610, -1), (2623, -1), (2643, -1), (2654, -1), (2668, -1), (2677, -1), (2686, -1), (2690, -1), (2699, -1), (2701, -1), (2703, -1), (2716, -2), (2717, -1), (2722, -1), (2976, 4), (2977, 4), (2980, 4), (2986, 4), (3048, 4), (3077, 4), (3078, 4), (3080, 4), (3083, 4), (3123, 4), (3213, 4), (3215, 4), (3216, 8), (3217, 4), (3226, 4), (3231, 4)]

def row2070 : Integer.Sparse (Fin 3237) := [(1503, 1), (1504, 1), (1506, 1), (1513, 1), (1598, 1), (2422, 1), (2423, 1), (2446, 1), (2470, 1), (2471, 1), (2475, 1), (2476, 1), (2508, 1), (2654, 1), (2668, 1), (2686, 1), (2690, 1), (2701, 1), (2703, 1), (2711, 1), (2712, 1), (2713, 2), (2716, 1), (2717, 1), (2719, 1), (2732, 1), (2746, 1)]

def row2071 : Integer.Sparse (Fin 3237) := [(1217, -1), (1224, -1), (1227, -2), (1509, -1), (1524, -1), (1525, -2), (1895, -1), (1907, -2), (1918, -1), (1948, -2), (2159, -1), (2369, -1), (2373, -2), (2458, -1), (2491, -2), (2567, -1), (2993, 4), (2994, 4), (2998, 8), (3059, 4), (3121, 4), (3133, 8), (3154, 8), (3159, 8), (3166, 8), (3191, 4), (3197, 8)]

def row2072 : Integer.Sparse (Fin 3237) := [(1509, 1), (1524, 1), (1525, 2), (1586, 1), (1587, 1), (1594, 1), (1605, 2), (1883, 1), (1884, 2), (1893, 2), (1895, 1), (1904, 2), (1905, 2), (1907, 2), (1918, 1), (1948, 2), (2133, 1), (2157, 2), (2159, 1)]

def row2073 : Integer.Sparse (Fin 3237) := [(1214, -1), (1219, -1), (1222, -1), (1226, -1), (1500, -1), (1510, -1), (1511, -1), (1516, -1), (1789, -1), (1896, -1), (1908, -1), (1909, -1), (1913, -1), (1933, -1), (1934, -1), (2160, -1), (2370, -1), (2376, -1), (2456, -1), (2490, -1), (2501, -1), (2574, -1), (2995, 4), (2996, 4), (2997, 4), (3000, 4), (3060, 4), (3096, 4), (3127, 4), (3152, 4), (3153, 4), (3155, 4), (3156, 4), (3160, 4), (3163, 4), (3164, 4), (3173, 4), (3180, 4), (3181, 4)]

def row2074 : Integer.Sparse (Fin 3237) := [(1500, 1), (1510, 1), (1511, 1), (1516, 1), (1596, 1), (1597, 1), (1602, 1), (1604, 1), (1613, 1), (1880, 1), (1881, 1), (1882, 1), (1888, 1), (1889, 1), (1894, 1), (1896, 1), (1897, 1), (1901, 1), (1902, 1), (1908, 1), (1909, 1), (1913, 1), (1933, 1), (1934, 1), (2128, 1), (2146, 1), (2147, 1), (2160, 1)]

def row2075 : Integer.Sparse (Fin 3237) := [(0, 198), (3, -30), (71, -120), (222, 360), (260, 90), (261, -210), (1654, -3240), (1655, -3240), (1657, -6480), (2392, -3240), (2393, -6480), (2396, -3240), (2562, -3240), (2565, -3240), (2624, -3240), (2685, -3240), (2687, -3240), (2705, -3240), (2755, -3240), (2757, -3240), (2759, -3240), (2794, -3240)]

def row2076 : Integer.Sparse (Fin 3237) := [(0, 54), (3, -6), (71, -24), (222, 72), (260, 18), (261, 30), (1343, -432), (1344, -864), (1398, -864), (1542, -432), (1544, -864), (1578, -864), (1648, -864), (1653, -1728), (2382, -864), (2388, -1728), (2554, -864), (2591, -864), (2611, -864), (2656, -864), (2671, -864), (2674, -864), (2691, -864), (2757, -864), (2764, -1728), (2798, -432), (2799, -864)]

def row2077 : Integer.Sparse (Fin 3237) := [(0, 984), (3, -120), (71, -480), (260, 360), (261, 120), (273, 1440), (1649, -12960), (1651, -12960), (1653, -12960), (1658, -12960), (1716, -6480), (1761, -6480), (2386, -12960), (2387, -12960), (2388, -12960), (2397, -12960), (2426, -6480), (2450, -6480), (2557, -12960), (2565, -6480), (2591, -6480), (2611, -6480), (2656, -6480), (2671, -6480), (2759, -6480), (2798, -6480), (2799, -12960), (2800, -6480), (2801, -12960), (2803, -12960)]

def row2078 : Integer.Sparse (Fin 3237) := [(1761, -1), (2097, -2), (2450, -1), (2556, -2), (2611, -1), (2671, -1), (2674, -1), (2682, -2), (2691, -1), (2697, -2), (2729, -2), (2742, -2), (2793, -4), (3073, 8), (3074, 8), (3075, 8), (3076, 8), (3100, 4), (3145, 4), (3154, 4), (3166, 4), (3183, 4), (3203, 4), (3223, 4), (3233, 4), (3234, 4)]

def row2079 : Integer.Sparse (Fin 3237) := [(1884, 1), (1886, 2), (1905, 1), (1945, 1), (2384, 2), (2389, 2), (2394, 2), (2435, 1), (2450, 1), (2499, 1), (2556, 2), (2663, 1), (2671, 1), (2691, 1), (2697, 2), (2721, 1), (2729, 2), (2785, 1), (2790, 1), (2793, 2)]

def row2080 : Integer.Sparse (Fin 3237) := [(1716, -1), (1761, -1), (2081, -2), (2426, -1), (2450, -1), (2555, -2), (2591, -1), (2611, -1), (2624, -1), (2656, -1), (2671, -1), (2685, -1), (2687, -1), (2705, -1), (2717, -2), (2722, -2), (2791, -4), (3068, 8), (3069, 8), (3070, 8), (3073, 8), (3214, 4), (3223, 8), (3233, 4)]

def row2081 : Integer.Sparse (Fin 3237) := [(2383, 2), (2384, 2), (2385, 2), (2390, 2), (2426, 1), (2450, 1), (2555, 2), (2656, 1), (2671, 1), (2687, 1), (2705, 1), (2714, 1), (2721, 2), (2722, 2), (2790, 1), (2791, 2)]

def row2082 : Integer.Sparse (Fin 3237) := [(1654, -1), (1756, -1), (1998, -1), (2392, -1), (2445, -1), (2540, -1), (2607, -2), (2609, -2), (2664, -2), (2667, -2), (2684, -1), (2694, -2), (2700, -1), (2702, -2), (2782, -2), (3003, 4), (3004, 4), (3008, 4), (3023, 8), (3070, 8), (3078, 8), (3141, 4), (3201, 8), (3204, 8), (3222, 4), (3228, 8)]

def row2083 : Integer.Sparse (Fin 3237) := [(1535, 1), (1537, 1), (1540, 1), (1566, 2), (2390, 2), (2392, 1), (2445, 1), (2470, 2), (2483, 1), (2540, 1), (2655, 2), (2664, 2), (2666, 2), (2667, 2), (2700, 1), (2702, 2), (2735, 1), (2740, 2), (2782, 1)]

def row2084 : Integer.Sparse (Fin 3237) := [(1649, -1), (1753, -1), (1993, -1), (2087, -1), (2386, -1), (2437, -1), (2542, -1), (2561, -1), (2607, -2), (2609, -1), (2611, -1), (2664, -2), (2667, -1), (2671, -1), (2682, -1), (2693, -1), (2697, -1), (2698, -1), (2782, -2), (2783, -1), (2786, -1), (3068, 4), (3070, 4), (3077, 4), (3078, 4), (3081, 4), (3097, 4), (3105, 4), (3142, 4), (3201, 4), (3203, 4), (3204, 4), (3235, 4)]

def row2085 : Integer.Sparse (Fin 3237) := [(2385, 1), (2386, 1), (2390, 1), (2422, 1), (2424, 1), (2437, 1), (2444, 1), (2470, 1), (2473, 1), (2487, 1), (2542, 1), (2561, 1), (2655, 1), (2663, 1), (2664, 2), (2666, 1), (2667, 1), (2671, 1), (2697, 1), (2698, 1), (2781, 1), (2782, 1), (2786, 1)]

def row2086 : Integer.Sparse (Fin 3237) := [(1648, -1), (1752, -1), (1815, -2), (1992, -1), (2382, -1), (2429, -1), (2481, -2), (2545, -1), (2610, -2), (2620, -1), (2658, -1), (2668, -2), (2681, -1), (2692, -1), (2693, -1), (2698, -1), (2723, -4), (3069, 8), (3079, 4), (3080, 8), (3120, 4), (3143, 4), (3202, 8), (3206, 8), (3222, 4)]

def row2087 : Integer.Sparse (Fin 3237) := [(2382, 1), (2383, 2), (2429, 1), (2471, 2), (2472, 1), (2481, 2), (2494, 1), (2511, 1), (2545, 1), (2658, 1), (2660, 2), (2661, 2), (2668, 2), (2692, 1), (2693, 1), (2723, 2), (2735, 1)]

def row2088 : Integer.Sparse (Fin 3237) := [(1657, -1), (1784, -1), (2001, -1), (2393, -1), (2447, -1), (2546, -1), (2590, -1), (2610, -1), (2620, -1), (2621, -1), (2654, -1), (2658, -1), (2665, -1), (2668, -1), (2677, -1), (2690, -1), (2699, -1), (2703, -1), (2704, -2), (2783, -1), (2786, -1), (3013, 4), (3014, 4), (3015, 4), (3035, 4), (3052, 4), (3073, 4), (3076, 4), (3083, 4), (3086, 4), (3147, 4), (3201, 4), (3206, 4), (3210, 4), (3211, 4), (3225, 4), (3230, 4), (3232, 4)]

def row2089 : Integer.Sparse (Fin 3237) := [(1564, 1), (1565, 1), (1570, 1), (1576, 1), (1615, 1), (2384, 1), (2393, 1), (2394, 1), (2447, 1), (2508, 1), (2510, 1), (2525, 1), (2546, 1), (2654, 1), (2655, 1), (2658, 1), (2661, 1), (2662, 1), (2665, 1), (2668, 1), (2670, 1), (2690, 1), (2703, 1), (2704, 1), (2739, 1), (2743, 1), (2748, 1), (2783, 1)]

def row2090 : Integer.Sparse (Fin 3237) := [(1653, -1), (1782, -1), (1997, -1), (2055, -1), (2388, -1), (2439, -1), (2548, -1), (2577, -1), (2589, -1), (2620, -1), (2621, -1), (2622, -1), (2653, -1), (2658, -1), (2665, -1), (2669, -1), (2676, -1), (2688, -1), (2699, -1), (2703, -1), (2783, -1), (2786, -1), (2787, -2), (3074, 4), (3076, 4), (3084, 4), (3085, 4), (3086, 4), (3101, 4), (3115, 4), (3148, 4), (3201, 4), (3209, 4), (3211, 4), (3232, 4)]

def row2091 : Integer.Sparse (Fin 3237) := [(2388, 1), (2389, 1), (2394, 1), (2439, 1), (2442, 1), (2443, 1), (2448, 1), (2509, 1), (2510, 1), (2533, 1), (2548, 1), (2577, 1), (2653, 1), (2655, 1), (2658, 1), (2659, 1), (2665, 1), (2669, 1), (2670, 1), (2688, 1), (2699, 1), (2783, 1), (2784, 1), (2787, 1)]

def row2092 : Integer.Sparse (Fin 3237) := [(1649, -1), (1655, -1), (1658, -2), (1993, -1), (1999, -1), (2002, -2), (2050, -1), (2058, -1), (2087, -2), (2386, -1), (2396, -1), (2397, -2), (2542, -1), (2543, -1), (2547, -2), (2551, -1), (2561, -2), (2569, -1), (2591, -2), (2607, -2), (2611, -2), (2656, -2), (2664, -2), (2671, -2), (2775, -1), (2779, -1), (2783, -2), (2786, -2), (2839, 4)]

def row2093 : Integer.Sparse (Fin 3237) := [(1648, -1), (1651, -1), (1653, -1), (1657, -1), (1712, -1), (1718, -1), (1815, -1), (1992, -1), (1997, -1), (2001, -1), (2047, -1), (2382, -1), (2387, -1), (2388, -1), (2393, -1), (2420, -1), (2427, -1), (2481, -1), (2545, -1), (2546, -1), (2548, -1), (2572, -1), (2589, -1), (2590, -1), (2606, -1), (2610, -1), (2620, -1), (2621, -1), (2622, -1), (2653, -1), (2654, -1), (2657, -1), (2658, -1), (2665, -1), (2668, -1), (2669, -1), (2676, -1), (2688, -1), (2723, -2), (2783, -1), (2786, -1), (2840, 4)]

def row2094 : Integer.Sparse (Fin 3237) := [(1339, -1), (1344, -1), (1345, -1), (1533, -1), (1544, -1), (1545, -1), (1781, -1), (1909, -2), (1913, -1), (1919, -1), (1920, -2), (1950, -2), (2177, -1), (2376, -2), (2456, -1), (2460, -2), (2503, -2), (2573, -1), (3075, 8), (3087, 4), (3088, 8), (3150, 4), (3152, 8), (3186, 4), (3190, 4), (3192, 8)]

def row2095 : Integer.Sparse (Fin 3237) := [(1533, 1), (1544, 1), (1545, 1), (1881, 2), (1886, 2), (1887, 2), (1909, 2), (1912, 1), (1913, 1), (1919, 1), (1920, 2), (1921, 1), (1950, 2), (2135, 2), (2165, 1), (2177, 1), (2178, 1)]

def row2096 : Integer.Sparse (Fin 3237) := [(1637, -1), (1638, -2), (1646, -1), (1704, -1), (1728, -2), (1982, -2), (1990, -1), (2023, -1), (2378, -1), (2379, -2), (2380, -1), (2401, -1), (2406, -2), (2541, -1), (2544, -2), (2568, -1), (2597, -2), (2601, -2), (2604, -2), (2618, -1), (2646, -2), (2647, -2), (2649, -2), (2651, -1), (2676, -2), (2688, -2), (2775, -1), (2779, -1), (2838, 4)]

def row2097 : Integer.Sparse (Fin 3237) := [(1676, -1), (1677, -2), (1705, -1), (1735, -2), (1796, -1), (2328, -1), (2329, -2), (2351, -1), (2400, -1), (2402, -2), (2588, -2), (2596, -2), (2600, -4), (2601, -2), (2627, -2), (2633, -2), (2635, -1), (2647, -2), (2672, -1), (2673, -1), (2674, -2), (2689, -2), (2691, -2), (2715, -1), (2836, 4)]

def row2098 : Integer.Sparse (Fin 3237) := [(2821, 2), (2822, 2), (2823, 4), (2826, 1), (2828, 2), (2830, 2), (2834, 2), (2835, 1), (2836, 4), (2837, 2), (2838, 2), (2839, 2), (2840, 4)]

def row2099 : Integer.Sparse (Fin 3237) := [(0, 189), (3, 60), (32, -45), (66, 240), (160, 720), (218, -720), (225, 480), (260, -180), (261, 930), (1211, -12960), (1223, -4320), (1430, -12960), (1461, -8640), (1515, -4320), (1990, -12960), (1998, -4320), (2540, -4320), (2541, -12960), (2627, -25920), (2642, -4320), (2643, -25920), (2701, -25920), (2733, -4320), (2749, -25920), (2752, -12960), (2760, -8640), (2763, -12960)]

def row2100 : Integer.Sparse (Fin 3237) := [(1836, -1), (2518, -1), (2635, -3), (2715, -3), (2726, -3), (2741, -3), (2767, -1), (2797, -1), (2984, 4), (2985, 12), (3054, 4), (3084, 12), (3087, 4), (3167, 12), (3215, 24), (3228, 12)]

def row2101 : Integer.Sparse (Fin 3237) := [(1498, 1), (1501, 3), (1582, 1), (1912, 1), (1914, 3), (2509, 3), (2518, 1), (2711, 6), (2715, 3), (2724, 3), (2741, 3), (2767, 1)]

def row2102 : Integer.Sparse (Fin 3237) := [(0, 391), (3, 120), (4, 15), (32, -280), (66, 400), (71, -160), (160, 640), (218, -480), (222, -960), (256, 320), (260, -360), (261, -270), (1214, -8640), (1217, -8640), (1466, -4320), (1500, -8640), (1509, -8640), (1589, -4320), (1992, -8640), (1993, -8640), (2542, -8640), (2545, -8640), (2553, -4320), (2633, -17280), (2635, -8640), (2689, -17280), (2715, -8640), (2726, -8640), (2741, -8640), (2752, -8640), (2753, -17280), (2762, -8640), (2768, -8640)]

def row2103 : Integer.Sparse (Fin 3237) := [(1217, -3), (1223, -1), (1509, -3), (1515, -1), (1907, -3), (1932, -3), (2159, -1), (2373, -3), (2489, -3), (2567, -1), (2992, 4), (2993, 12), (3058, 4), (3159, 24), (3162, 12), (3179, 12)]

def row2104 : Integer.Sparse (Fin 3237) := [(1509, 3), (1515, 1), (1581, 1), (1584, 1), (1586, 3), (1893, 6), (1900, 3), (1907, 3), (1932, 3), (2145, 3), (2159, 1)]

def row2105 : Integer.Sparse (Fin 3237) := [(0, 319), (3, 60), (4, 15), (32, -220), (66, -80), (71, 80), (160, -320), (222, -240), (256, -320), (260, -180), (261, 430), (273, -480), (1648, -8640), (1649, -8640), (2382, -8640), (2386, -8640), (2553, -4320), (2674, -8640), (2691, -8640), (2759, -4320), (2799, -8640), (2802, -8640)]

def row2106 : Integer.Sparse (Fin 3237) := [(2821, 8), (2827, 2), (2836, 12), (2839, 8)]

def row2107 : Integer.Sparse (Fin 3237) := [(0, 303), (3, 60), (4, -15), (32, -60), (66, 480), (160, 960), (218, -720), (225, 480), (260, -180), (261, 1500), (2060, -12960), (2550, -12960), (2554, -12960), (2623, -12960), (2684, -12960), (2686, -12960), (2700, -12960), (2752, -12960), (2763, -12960)]

def row2108 : Integer.Sparse (Fin 3237) := [(0, 225), (3, -60), (4, 15), (32, -270), (66, -240), (71, -240), (160, -1440), (222, 720), (225, -480), (256, -960), (260, 180), (261, 210), (1336, -3240), (1339, -12960), (1388, -12960), (1529, -3240), (1533, -12960), (1548, -12960), (2589, -12960), (2606, -12960), (2653, -12960), (2657, -12960), (2716, -25920), (2757, -12960), (2762, -12960)]

def row2109 : Integer.Sparse (Fin 3237) := [(1756, -1), (2445, -1), (2609, -1), (2667, -1), (2682, -2), (2694, -2), (2697, -2), (2702, -2), (2726, -1), (2741, -1), (3005, 4), (3006, 4), (3008, 4), (3026, 8), (3101, 8), (3143, 4), (3152, 8), (3155, 4), (3169, 4), (3201, 8), (3206, 8), (3222, 4), (3226, 8), (3229, 8)]

def row2110 : Integer.Sparse (Fin 3237) := [(1530, 1), (1534, 1), (1537, 1), (1553, 2), (1881, 2), (1888, 1), (1923, 1), (2442, 2), (2445, 1), (2494, 1), (2655, 2), (2661, 2), (2667, 1), (2697, 2), (2702, 2), (2719, 2), (2726, 1), (2735, 1), (2737, 2)]

def row2111 : Integer.Sparse (Fin 3237) := [(2825, 1), (2826, 4), (2828, 4), (2834, 4), (2836, 4), (2838, 4), (2839, 4), (2840, 4)]

def row2112 : Integer.Sparse (Fin 3237) := [(1010, 4), (1017, 2), (2810, -1)]

def row2113 : Integer.Sparse (Fin 3237) := [(402, 4), (1017, 1), (2810, -1)]

def row2114 : Integer.Sparse (Fin 3237) := [(997, 1), (1008, 3), (1013, 1), (1016, 1), (2808, -1)]

def row2115 : Integer.Sparse (Fin 3237) := [(992, 3), (997, 1), (1013, 2), (2808, -1)]

def row2116 : Integer.Sparse (Fin 3237) := [(399, 3), (406, 1), (1013, 1), (2808, -1)]

def row2117 : Integer.Sparse (Fin 3237) := [(1003, 1), (1005, 3), (1007, 1), (1015, 1), (2809, -1)]

def row2118 : Integer.Sparse (Fin 3237) := [(999, 3), (1003, 1), (1014, 1), (1015, 1), (2809, -1)]

def row2119 : Integer.Sparse (Fin 3237) := [(1009, 3), (1014, 2), (1015, 1), (2809, -1)]

def row2120 : Integer.Sparse (Fin 3237) := [(972, 3), (1014, 1), (1015, 1), (2809, -1)]

def row2121 : Integer.Sparse (Fin 3237) := [(971, 3), (1003, 1), (1014, 1), (2809, -1)]

def row2122 : Integer.Sparse (Fin 3237) := [(990, 2), (994, 2), (996, 1), (1011, 1), (2806, -1)]

def row2123 : Integer.Sparse (Fin 3237) := [(985, 1), (1004, 2), (1006, 2), (1011, 1), (2806, -1)]

def row2124 : Integer.Sparse (Fin 3237) := [(981, 2), (985, 1), (994, 2), (1011, 1), (2806, -1)]

def row2125 : Integer.Sparse (Fin 3237) := [(987, 2), (989, 1), (995, 1), (1001, 2), (2807, -1)]

def row2126 : Integer.Sparse (Fin 3237) := [(995, 1), (998, 2), (1001, 1), (1002, 1), (1012, 1), (2807, -1)]

def row2127 : Integer.Sparse (Fin 3237) := [(991, 2), (995, 2), (1012, 2), (2807, -1)]

def row2128 : Integer.Sparse (Fin 3237) := [(977, 1), (979, 1), (983, 3), (1000, 1), (2805, -1)]

def row2129 : Integer.Sparse (Fin 3237) := [(980, 1), (983, 1), (984, 1), (993, 3), (2805, -1)]

def row2130 : Integer.Sparse (Fin 3237) := [(983, 1), (986, 1), (988, 2), (993, 1), (1000, 1), (2805, -1)]

def row2131 : Integer.Sparse (Fin 3237) := [(967, 1), (993, 3), (1000, 1), (2805, -1)]

def row2132 : Integer.Sparse (Fin 3237) := [(978, 2), (982, 4), (2804, -1)]

def row2133 : Integer.Sparse (Fin 3237) := [(973, 1), (982, 4), (2804, -1)]

def row2134 : Integer.Sparse (Fin 3237) := [(1128, 2), (1132, 2), (1135, 2), (2814, -1)]

def row2135 : Integer.Sparse (Fin 3237) := [(1132, 2), (2272, 2), (2285, 2), (2814, -1)]

def row2136 : Integer.Sparse (Fin 3237) := [(1125, 2), (1127, 1), (1134, 1), (1169, 1), (1526, 1), (2815, -1)]

def row2137 : Integer.Sparse (Fin 3237) := [(1119, 2), (1123, 1), (1133, 1), (1161, 1), (2287, 1), (2815, -1)]

def row2138 : Integer.Sparse (Fin 3237) := [(1129, 2), (1133, 1), (1134, 1), (1174, 1), (2286, 1), (2815, -1)]

def row2139 : Integer.Sparse (Fin 3237) := [(1123, 1), (1508, 2), (1526, 1), (1606, 1), (2287, 1), (2815, -1)]

def row2140 : Integer.Sparse (Fin 3237) := [(1134, 1), (1526, 1), (2278, 2), (2286, 1), (2287, 1), (2815, -1)]

def row2141 : Integer.Sparse (Fin 3237) := [(1133, 1), (2282, 2), (2286, 2), (2287, 1), (2815, -1)]

def row2142 : Integer.Sparse (Fin 3237) := [(2247, 1), (2262, 2), (2286, 1), (2287, 1), (2815, -1)]

def row2143 : Integer.Sparse (Fin 3237) := [(1258, 2), (1264, 1), (1526, 1), (2286, 1), (2815, -1)]

def row2144 : Integer.Sparse (Fin 3237) := [(1130, 1), (1543, 1), (2265, 1), (2274, 2), (2283, 1), (2812, -1)]

def row2145 : Integer.Sparse (Fin 3237) := [(1121, 1), (1885, 1), (2268, 1), (2275, 1), (2280, 2), (2813, -1)]

def row2146 : Integer.Sparse (Fin 3237) := [(1131, 1), (2271, 1), (2275, 2), (2284, 2), (2813, -1)]

def row2147 : Integer.Sparse (Fin 3237) := [(1520, 2), (1522, 2), (1528, 2), (2824, -1)]

def row2148 : Integer.Sparse (Fin 3237) := [(1514, 2), (1518, 1), (1527, 1), (1614, 1), (2549, 1), (2824, -1)]

def row2149 : Integer.Sparse (Fin 3237) := [(1523, 2), (1527, 1), (1528, 1), (1627, 1), (2399, 1), (2824, -1)]

def row2150 : Integer.Sparse (Fin 3237) := [(1527, 1), (2391, 2), (2398, 1), (2399, 1), (2549, 1), (2824, -1)]

def row2151 : Integer.Sparse (Fin 3237) := [(2395, 2), (2398, 2), (2399, 2), (2824, -1)]

def row2152 : Integer.Sparse (Fin 3237) := [(1528, 2), (2399, 2), (2474, 2), (2824, -1)]

def row2153 : Integer.Sparse (Fin 3237) := [(1506, 1), (1510, 1), (1512, 1), (1524, 1), (1604, 1), (2427, 1), (2822, -1)]

def row2154 : Integer.Sparse (Fin 3237) := [(1519, 1), (1521, 2), (1524, 1), (1539, 1), (1545, 1), (2822, -1)]

def row2155 : Integer.Sparse (Fin 3237) := [(1499, 1), (1502, 1), (1510, 2), (1587, 1), (2543, 1), (2822, -1)]

def row2156 : Integer.Sparse (Fin 3237) := [(2385, 1), (2387, 2), (2389, 1), (2396, 1), (2427, 1), (2822, -1)]

def row2157 : Integer.Sparse (Fin 3237) := [(1540, 1), (1544, 1), (1545, 1), (1576, 2), (2396, 1), (2822, -1)]

def row2158 : Integer.Sparse (Fin 3237) := [(1544, 1), (2387, 2), (2396, 1), (2543, 1), (2822, -1)]

def row2159 : Integer.Sparse (Fin 3237) := [(1502, 1), (1535, 1), (1544, 1), (1565, 2), (2543, 1), (2822, -1)]

def row2160 : Integer.Sparse (Fin 3237) := [(1524, 1), (1545, 1), (2396, 1), (2427, 2), (2472, 1), (2822, -1)]

def row2161 : Integer.Sparse (Fin 3237) := [(1503, 1), (1505, 1), (1511, 1), (1516, 1), (1597, 1), (2546, 1), (2823, -1)]

def row2162 : Integer.Sparse (Fin 3237) := [(1513, 1), (1516, 1), (1517, 1), (1525, 1), (1613, 1), (2548, 1), (2823, -1)]

def row2163 : Integer.Sparse (Fin 3237) := [(1507, 1), (1511, 2), (1525, 1), (1605, 1), (2547, 1), (2823, -1)]

def row2164 : Integer.Sparse (Fin 3237) := [(1886, 1), (2383, 1), (2388, 1), (2393, 2), (2546, 1), (2823, -1)]

def row2165 : Integer.Sparse (Fin 3237) := [(1541, 2), (2425, 4), (2825, -1)]

def row2166 : Integer.Sparse (Fin 3237) := [(0, 9), (32, -25), (160, -80), (225, -40), (256, -160), (261, 170)]

def row2167 : Integer.Sparse (Fin 3237) := [(0, -1), (3, -8), (4, 1), (260, 12), (261, -4)]

def row2168 : Integer.Sparse (Fin 3237) := [(0, -1), (3, 3), (32, -8), (66, -16), (71, -8), (160, -64), (218, 12), (222, 24), (225, -24), (256, -32), (261, 18)]

def row2169 : Integer.Sparse (Fin 3237) := [(0, -9), (3, 30), (32, -110), (66, -40), (71, -200), (160, -160), (222, 120), (256, -160), (261, 205), (273, 240)]

def row2170 : Integer.Sparse (Fin 3237) := [(0, -4), (32, -25), (160, -320), (162, -80), (225, -160), (256, -160), (261, 95)]

def row2171 : Integer.Sparse (Fin 3237) := [(0, -11), (32, -45), (160, -800), (225, -320), (252, 120), (255, -160), (256, -480), (261, 250)]

def row2172 : Integer.Sparse (Fin 3237) := [(0, -9), (32, -70), (160, -480), (225, -80), (255, -80), (256, -400), (261, 315), (274, 240)]

def row2173 : Integer.Sparse (Fin 3237) := [(0, 1), (32, 4), (195, 18), (198, 72), (218, -48), (252, -96), (260, 9), (261, -8), (273, -24), (274, -96)]

def row2174 : Integer.Sparse (Fin 3237) := [(0, 149), (32, 285), (160, 2080), (196, 720), (204, 1440), (218, -240), (222, -720), (225, 800), (252, -480), (256, 2880), (260, 180), (261, -1760), (273, -480), (274, -960)]

def row2175 : Integer.Sparse (Fin 3237) := [(0, -11), (32, 80), (160, 640), (197, 180), (198, 360), (218, -240), (225, 240), (256, 320), (260, 45), (261, -150), (273, -120)]

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

def row2176 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 45), (160, 1120), (199, 360), (211, 720), (225, 440), (256, 1080), (261, -890)]

def row2177 : Integer.Sparse (Fin 3237) := [(0, 12), (32, 33), (160, 320), (196, 144), (198, 72), (218, -72), (222, -48), (225, 192), (252, -144), (256, 224), (260, 18), (261, -121), (273, -24), (274, -144)]

def row2178 : Integer.Sparse (Fin 3237) := [(0, 3), (32, 11), (160, 80), (198, 36), (203, 36), (204, 36), (211, 36), (222, -60), (225, 20), (256, 80), (260, 9), (261, -65), (273, -12), (274, -48)]

def row2179 : Integer.Sparse (Fin 3237) := [(0, 93), (32, 210), (160, 2880), (210, 720), (211, 720), (225, 1520), (256, 2400), (261, -1715), (274, -480)]

def row2180 : Integer.Sparse (Fin 3237) := [(0, 16), (32, 65), (160, 960), (199, 360), (225, 360), (252, -240), (256, 600), (261, -315), (274, -240)]

def row2181 : Integer.Sparse (Fin 3237) := [(0, -11), (3, 260), (4, -15), (32, -250), (66, -480), (68, -160), (71, -480), (159, 720), (160, -1200), (162, -320), (165, -240), (225, -480), (256, -240), (261, 220)]

def row2182 : Integer.Sparse (Fin 3237) := [(0, -32), (3, 60), (4, -15), (32, -60), (68, -240), (160, -2160), (162, -160), (224, 720), (225, -240), (255, -960), (256, -960), (261, 615)]

def row2183 : Integer.Sparse (Fin 3237) := [(0, -7), (3, 160), (4, -20), (32, -70), (66, -80), (68, -80), (71, -160), (160, -480), (165, -160), (255, -160), (256, -160), (261, 125)]

def row2184 : Integer.Sparse (Fin 3237) := [(0, -2), (3, 52), (4, -8), (32, -11), (66, -16), (68, -80), (71, -32), (160, -304), (162, -208), (165, -64), (219, 48), (225, -64), (251, 96), (255, -64), (256, -64), (261, 55)]

def row2185 : Integer.Sparse (Fin 3237) := [(0, -11), (3, 160), (4, -15), (32, -95), (66, -240), (68, -80), (71, -240), (160, -720), (255, -240), (256, -240), (261, 215)]

def row2186 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 10), (66, -160), (68, -80), (160, -400), (162, -240), (218, 360), (219, 240), (225, -240), (252, 360), (261, 5)]

def row2187 : Integer.Sparse (Fin 3237) := [(0, -7), (17, -80), (32, -15), (160, -720), (162, -960), (225, -360), (261, 180)]

def row2188 : Integer.Sparse (Fin 3237) := [(0, -7), (24, 120), (29, -80), (32, -30), (160, -680), (162, -160), (225, -120), (255, -280), (256, -240), (261, 145)]

def row2189 : Integer.Sparse (Fin 3237) := [(0, -19), (24, 240), (32, -75), (160, -640), (225, -200), (252, 240), (255, -80), (256, -480), (261, 300), (274, 480)]

def row2190 : Integer.Sparse (Fin 3237) := [(0, 157), (24, -960), (32, 585), (148, 720), (160, 5280), (162, 560), (225, 2240), (252, -1200), (256, 3520), (261, -2040), (274, -2880)]

def row2191 : Integer.Sparse (Fin 3237) := [(0, 59), (3, -80), (24, -480), (32, 320), (66, 80), (71, 320), (139, 1440), (159, -480), (160, 1040), (218, -240), (219, -240), (225, 480), (252, -240), (256, 480), (260, 180), (261, -575), (273, -480), (274, -480)]

def row2192 : Integer.Sparse (Fin 3237) := [(0, 29), (24, -192), (32, 99), (135, 144), (139, 288), (160, 896), (162, 32), (225, 352), (252, -96), (255, 112), (256, 512), (261, -334), (274, -336)]

def row2193 : Integer.Sparse (Fin 3237) := [(0, 128), (32, 405), (135, 720), (138, 720), (139, 720), (142, 720), (160, 4480), (225, 1360), (252, -960), (255, 960), (256, 2960), (261, -1575), (274, -1680)]

def row2194 : Integer.Sparse (Fin 3237) := [(0, 58), (3, -30), (24, -480), (32, 235), (66, 40), (71, 80), (146, 360), (147, 720), (159, -360), (160, 1280), (218, -240), (222, -720), (224, -240), (225, 560), (252, -600), (256, 920), (260, 300), (261, -605), (273, -480), (274, -1200)]

def row2195 : Integer.Sparse (Fin 3237) := [(0, 141), (3, -60), (32, 580), (66, 80), (71, 160), (145, 720), (147, 1440), (159, -720), (160, 3600), (162, 320), (218, -480), (222, -1440), (224, -480), (225, 1440), (256, 2560), (260, 600), (261, -1765), (273, -960), (274, -1920)]

def row2196 : Integer.Sparse (Fin 3237) := [(0, 109), (3, -120), (32, 565), (66, 160), (71, 320), (135, 720), (160, 2880), (218, -480), (222, -1440), (224, -480), (225, 800), (255, 400), (256, 1760), (260, 600), (261, -1300), (273, -960), (274, -1200)]

def row2197 : Integer.Sparse (Fin 3237) := [(0, 56), (3, -80), (32, 305), (66, 160), (71, 240), (139, 360), (142, 360), (159, -480), (160, 1760), (222, -480), (225, 440), (251, -240), (255, 160), (256, 1120), (260, 180), (261, -675), (273, -240), (274, -720)]

def row2198 : Integer.Sparse (Fin 3237) := [(0, 67), (3, -60), (24, -960), (32, 185), (66, 80), (71, 160), (99, 720), (101, 1440), (160, 3200), (162, 1200), (219, -720), (225, 1040), (252, -960), (255, 640), (256, 960), (261, -1010), (274, -960)]

def row2199 : Integer.Sparse (Fin 3237) := [(0, 8), (3, -44), (24, -384), (32, 109), (66, 48), (71, 160), (97, 144), (101, 288), (102, 288), (159, -192), (160, 624), (218, -48), (219, -240), (224, -144), (225, 96), (252, -96), (255, 128), (256, 192), (260, 36), (261, -151), (273, -96), (274, -192)]

def row2200 : Integer.Sparse (Fin 3237) := [(0, 19), (3, -12), (32, 91), (66, 16), (71, 32), (98, 144), (102, 288), (160, 928), (162, 32), (225, 48), (251, -144), (255, 368), (256, 512), (261, -288), (272, 288)]

def row2201 : Integer.Sparse (Fin 3237) := [(0, 37), (3, -80), (32, 255), (66, 80), (71, 320), (99, 360), (102, 720), (159, -480), (160, 1920), (162, 880), (218, -120), (219, -240), (224, -360), (225, 720), (255, 160), (256, 320), (260, 90), (261, -580), (273, -240)]

def row2202 : Integer.Sparse (Fin 3237) := [(0, 16), (24, -192), (32, 93), (106, 144), (115, 288), (160, 896), (162, 448), (225, 384), (255, 112), (256, 304), (261, -255), (274, -192)]

def row2203 : Integer.Sparse (Fin 3237) := [(0, 17), (32, 76), (160, 1008), (209, 144), (255, 528), (256, 480), (261, -309), (272, 144)]

def row2204 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -32), (24, -192), (32, 82), (66, 64), (71, 96), (98, 144), (101, 144), (102, 144), (115, 144), (159, -192), (160, 720), (162, 128), (222, -96), (224, -144), (225, 160), (251, -96), (255, 176), (256, 288), (260, 36), (261, -179), (273, -48), (274, -96)]

def row2205 : Integer.Sparse (Fin 3237) := [(0, 1), (3, -10), (24, -480), (32, 70), (66, 80), (97, 720), (146, 720), (159, -240), (160, 1200), (195, 360), (196, 1440), (218, -840), (219, -240), (222, -480), (224, -240), (225, 720), (252, -840), (256, 400), (260, 120), (261, -145)]

def row2206 : Integer.Sparse (Fin 3237) := [(0, 83), (32, 145), (99, 1440), (148, 720), (160, 5280), (162, 720), (196, 1440), (197, 720), (199, 2880), (218, -480), (222, -480), (224, -480), (225, 1760), (252, -720), (256, 1920), (260, 60), (261, -1010)]

def row2207 : Integer.Sparse (Fin 3237) := [(0, 88), (3, -20), (32, 255), (66, 80), (71, 80), (98, 1440), (145, 720), (146, 720), (159, -480), (160, 4080), (196, 720), (199, 720), (203, 1440), (210, 1440), (218, -240), (222, -1440), (225, 880), (251, -480), (252, -240), (255, 480), (256, 1760), (260, 180), (261, -1245), (274, -960)]

def row2208 : Integer.Sparse (Fin 3237) := [(0, 79), (3, -20), (32, 195), (66, 80), (71, 120), (138, 720), (139, 720), (146, 360), (159, -120), (160, 1040), (198, 360), (204, 720), (218, -120), (222, -600), (225, 160), (252, -360), (255, 80), (256, 1320), (260, 90), (261, -810), (273, -360), (274, -720)]

def row2209 : Integer.Sparse (Fin 3237) := [(0, 1), (1, -100), (2, 5), (32, -25), (261, -25)]

def row2210 : Integer.Sparse (Fin 3237) := [(0, 1), (1, -16), (3, -120), (4, 15), (31, 240), (32, 36), (260, 180), (261, -24)]

def row2211 : Integer.Sparse (Fin 3237) := [(0, 1), (1, 40), (3, 320), (4, -30), (32, -150), (34, -240), (35, -80), (37, -480), (66, -480), (68, -160), (71, -480), (160, -240), (261, -25)]

def row2212 : Integer.Sparse (Fin 3237) := [(0, -1), (1, 20), (3, -20), (32, -10), (34, -320), (35, -160), (66, -480), (68, -320), (153, 720), (154, 480), (160, -480), (162, -160), (218, 720), (225, -320), (261, 55)]

def row2213 : Integer.Sparse (Fin 3237) := [(0, -9), (1, 20), (3, 260), (4, -30), (32, -160), (34, -240), (35, -160), (37, -80), (66, -720), (68, -640), (71, -240), (156, 720), (160, -1280), (165, -480), (217, 480), (222, 720), (255, -480), (256, -480), (261, 135)]

def row2214 : Integer.Sparse (Fin 3237) := [(0, 3), (1, 10), (3, 210), (4, -30), (32, -90), (34, -120), (35, -120), (66, -480), (68, -720), (154, 360), (160, -1440), (162, -1240), (165, -480), (215, 240), (218, 360), (219, 720), (225, -600), (261, 105)]

def row2215 : Integer.Sparse (Fin 3237) := [(0, -4), (1, 20), (3, 280), (4, -15), (32, -230), (34, -160), (37, -320), (66, -480), (71, -480), (153, 240), (156, 960), (159, 480), (160, -640), (165, -160), (222, 480), (256, -160), (260, -60), (261, 45)]

def row2216 : Integer.Sparse (Fin 3237) := [(0, -14), (1, 20), (3, 440), (4, -45), (32, -250), (34, -80), (37, -400), (66, -160), (71, -800), (156, 240), (160, -320), (165, -160), (260, -60), (261, 65), (266, 960), (273, 480)]

def row2217 : Integer.Sparse (Fin 3237) := [(0, -2), (1, 20), (3, 460), (4, -65), (32, -60), (34, -80), (35, -80), (37, -320), (66, -160), (68, -400), (71, -480), (154, 240), (160, -880), (162, -400), (165, -320), (217, 960), (222, 480), (224, 240), (251, 960), (255, -320), (256, -320), (261, 95)]

def row2218 : Integer.Sparse (Fin 3237) := [(0, -1), (3, 265), (4, -15), (32, -140), (64, 180), (66, -600), (68, -320), (69, -60), (71, -480), (160, -480), (162, -160), (225, -120), (261, 35)]

def row2219 : Integer.Sparse (Fin 3237) := [(0, -1), (3, 680), (4, -90), (32, -205), (66, -480), (68, -1120), (71, -480), (160, -1200), (165, -1200), (253, 720), (254, -240), (255, -480), (256, -240), (261, 10)]

def row2220 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 90), (4, -15), (32, -50), (66, -40), (68, -160), (69, -120), (71, -80), (160, -160), (162, -160), (163, -160), (165, -320), (220, 60), (225, -20), (227, 240), (261, -30)]

def row2221 : Integer.Sparse (Fin 3237) := [(0, -1), (3, 10), (32, -5), (64, 360), (66, -240), (68, -320), (69, -120), (157, 360), (160, -480), (162, -640), (163, -120), (225, -240), (261, -10)]

def row2222 : Integer.Sparse (Fin 3237) := [(0, -9), (3, 140), (4, -30), (32, 90), (66, -240), (68, -1520), (160, -3360), (162, -1680), (165, -240), (219, 2160), (225, -960), (250, 480), (251, 1440), (252, 720), (253, 720), (254, -240), (255, -1440), (256, -1200), (261, 525)]

def row2223 : Integer.Sparse (Fin 3237) := [(0, -19), (3, 240), (4, -40), (32, -105), (68, -480), (160, -1360), (165, -400), (224, 480), (253, 240), (254, -80), (255, -640), (256, -560), (260, -120), (261, 270), (267, 480), (268, 480), (274, 480)]

def row2224 : Integer.Sparse (Fin 3237) := [(3, 44), (4, -8), (32, -13), (66, -48), (68, -208), (69, -64), (160, -400), (162, -368), (163, -64), (165, -128), (219, 144), (220, 48), (225, -144), (227, 96), (251, 96), (255, -64), (256, -64), (261, 35)]

def row2225 : Integer.Sparse (Fin 3237) := [(0, 7), (3, 1240), (4, -160), (8, 720), (10, -320), (32, -465), (66, -960), (68, -1520), (71, -960), (160, -1680), (162, -1120), (163, -240), (165, -1920), (225, -240), (261, -140)]

def row2226 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 240), (4, -20), (27, -80), (32, -120), (61, 240), (66, -480), (68, -400), (71, -320), (160, -480), (165, -160), (255, -160), (256, -80), (261, -5)]

def row2227 : Integer.Sparse (Fin 3237) := [(0, 12), (3, 20), (4, -5), (10, -160), (15, 480), (17, -160), (24, 720), (29, -480), (32, -15), (68, -240), (160, -1760), (162, -2000), (224, 720), (225, -720), (255, -560), (261, 50)]

def row2228 : Integer.Sparse (Fin 3237) := [(0, 2), (3, 8), (4, -1), (20, 48), (21, 96), (24, 192), (29, -32), (32, -5), (68, -32), (160, -256), (162, -224), (165, -32), (224, 96), (225, -96), (252, 48), (255, -64), (261, 6)]

def row2229 : Integer.Sparse (Fin 3237) := [(0, 8), (3, 60), (4, -15), (20, 240), (23, 480), (24, 480), (27, -160), (29, -320), (32, -15), (66, -160), (68, -480), (160, -1120), (162, -800), (218, 240), (219, 480), (224, 480), (225, -320), (255, -480), (261, 40)]

def row2230 : Integer.Sparse (Fin 3237) := [(0, -2), (3, 16), (4, -2), (21, 48), (24, 48), (26, 96), (27, -32), (29, -112), (32, -13), (66, -16), (68, -64), (71, -16), (160, -528), (162, -80), (165, -16), (222, 48), (224, 144), (225, -16), (251, 96), (255, -336), (256, -224), (261, 67)]

def row2231 : Integer.Sparse (Fin 3237) := [(0, 9), (3, 60), (4, -5), (8, 720), (10, -400), (15, 720), (17, -320), (29, -480), (32, -65), (68, -240), (160, -1440), (162, -2640), (163, -240), (165, -480), (225, -720), (255, -240), (261, -5)]

def row2232 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 14), (4, -2), (10, -16), (16, 48), (17, -16), (24, 72), (32, -7), (66, -24), (68, -72), (160, -144), (162, -160), (165, -48), (219, 72), (225, -48), (255, -24)]

def row2233 : Integer.Sparse (Fin 3237) := [(0, -16), (3, 120), (4, -5), (21, 240), (24, 960), (27, -160), (29, -400), (32, -240), (61, 480), (66, -480), (68, -560), (71, -160), (150, 480), (159, 480), (160, -3440), (162, -320), (165, -240), (225, -320), (252, 240), (255, -1600), (256, -1280), (261, 485), (274, 480)]

def row2234 : Integer.Sparse (Fin 3237) := [(3, 44), (4, -5), (21, 48), (27, -32), (29, -80), (32, -35), (66, -112), (68, -160), (71, -32), (159, 96), (160, -448), (162, -272), (165, -112), (219, 48), (225, -128), (255, -160), (256, -64), (261, 42)]

def row2235 : Integer.Sparse (Fin 3237) := [(0, -9), (23, 240), (24, 1440), (27, -80), (29, -320), (32, -120), (61, 240), (66, -80), (68, -160), (160, -2560), (162, -480), (213, -480), (218, 240), (219, 480), (225, -800), (252, 720), (255, -880), (256, -880), (261, 345), (274, 480)]

def row2236 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 5), (8, 120), (10, -20), (15, 60), (24, 360), (29, -80), (32, -40), (68, -20), (159, 180), (160, -620), (162, -340), (163, -20), (165, -60), (212, -120), (224, 60), (225, -260), (252, 60), (255, -100), (256, -140), (260, -15), (261, 65), (274, 120)]

def row2237 : Integer.Sparse (Fin 3237) := [(0, 5), (3, -15), (32, 44), (59, 36), (60, 72), (64, -36), (66, 20), (71, 40), (160, 160), (162, 32), (218, -120), (222, -336), (224, -192), (225, 56), (256, 64), (260, 123), (261, -73), (273, -192)]

def row2238 : Integer.Sparse (Fin 3237) := [(0, 17), (3, -620), (4, 15), (32, 730), (55, 720), (56, 1440), (66, 1120), (68, 160), (71, 1760), (159, -3600), (160, 3040), (218, -480), (219, -960), (222, -1440), (224, -480), (225, 400), (251, -1920), (253, -720), (255, 480), (256, 1040), (260, 600), (261, -570), (273, -960)]

def row2239 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -350), (4, 20), (8, -480), (32, 240), (42, 180), (44, 360), (45, 360), (64, -180), (66, 600), (68, 240), (71, 520), (159, -480), (160, 560), (162, 240), (165, 160), (218, -60), (219, -240), (220, -180), (225, 180), (260, 45), (261, 20), (273, -120)]

def row2240 : Integer.Sparse (Fin 3237) := [(0, -14), (3, -2280), (4, 205), (32, 1255), (61, -960), (66, 3040), (68, 2240), (71, 2720), (75, 720), (79, 1440), (89, 1440), (160, 3120), (165, 2320), (253, -720), (255, 480), (256, 400), (261, 260)]

def row2241 : Integer.Sparse (Fin 3237) := [(0, -17), (3, -1580), (4, 95), (8, -1920), (32, 990), (43, 720), (44, 720), (45, 720), (51, 1440), (64, -720), (66, 2800), (68, 1440), (71, 2640), (159, -1920), (160, 2880), (162, 640), (165, 640), (222, -480), (225, 400), (227, -720), (251, -960), (256, 320), (260, 180), (261, 80), (273, -240)]

def row2242 : Integer.Sparse (Fin 3237) := [(0, -17), (3, -2160), (4, 185), (32, 1440), (43, 720), (45, 1440), (61, -960), (66, 2480), (68, 2400), (71, 2400), (89, 2880), (160, 3840), (162, 640), (165, 3200), (225, 480), (227, -720), (261, 280)]

def row2243 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -1240), (4, 95), (32, 950), (61, -1920), (66, 1520), (68, 960), (71, 1600), (74, 720), (79, 2880), (89, 1440), (160, 3360), (165, 1280), (253, -1440), (255, 960), (256, 720), (261, 10)]

def row2244 : Integer.Sparse (Fin 3237) := [(0, 13), (3, -100), (8, -480), (32, 285), (59, 720), (64, -240), (66, 560), (71, 160), (107, 1440), (145, 2880), (146, 1440), (148, 720), (159, -1440), (160, 4800), (162, 1520), (218, -1920), (222, -1440), (224, -960), (225, 1920), (252, -240), (256, 800), (260, 420), (261, -580)]

def row2245 : Integer.Sparse (Fin 3237) := [(0, 8), (3, -12), (4, 1), (24, -96), (32, 37), (66, 64), (68, 64), (121, 288), (131, 144), (135, 576), (148, 144), (160, 800), (162, 80), (165, 32), (218, -96), (224, -96), (225, 592), (252, -384), (255, 128), (256, 352), (261, -124)]

def row2246 : Integer.Sparse (Fin 3237) := [(0, 64), (3, -260), (4, 5), (32, 515), (55, 720), (61, -480), (66, 480), (71, 800), (125, 1440), (127, 1440), (135, 720), (142, 1440), (143, 1440), (159, -1440), (160, 3760), (165, 80), (218, -240), (222, -480), (225, 240), (251, -960), (253, -240), (255, 880), (256, 1760), (260, 60), (261, -710), (274, -1680)]

def row2247 : Integer.Sparse (Fin 3237) := [(0, 6), (3, -28), (4, 2), (24, -336), (32, 83), (61, -96), (66, 112), (68, 80), (71, 16), (108, 144), (121, 144), (131, 288), (135, 288), (142, 288), (143, 288), (148, 144), (159, -96), (160, 832), (162, 96), (165, 64), (218, -48), (222, -48), (224, -96), (225, 320), (252, -336), (255, 128), (256, 368), (261, -189), (274, -336)]

def row2248 : Integer.Sparse (Fin 3237) := [(0, -1), (3, -40), (4, 1), (8, -144), (32, 56), (42, 72), (45, 144), (64, -72), (66, 80), (68, 32), (71, 80), (99, 72), (102, 144), (107, 144), (108, 288), (116, 288), (159, -48), (160, 464), (162, 192), (165, 48), (220, -24), (222, -48), (224, -72), (225, 184), (255, 32), (256, 80), (261, -56)]

def row2249 : Integer.Sparse (Fin 3237) := [(0, 31), (3, -20), (4, 1), (32, 90), (66, 32), (68, 32), (71, 32), (108, 288), (131, 144), (135, 288), (138, 576), (160, 768), (165, 32), (222, -96), (224, -96), (225, 144), (252, -240), (255, 160), (256, 704), (261, -362), (274, -768)]

def row2250 : Integer.Sparse (Fin 3237) := [(0, 68), (3, -180), (4, 5), (32, 540), (59, 720), (64, -240), (66, 880), (68, 240), (71, 160), (108, 1440), (131, 1440), (135, 2880), (160, 5040), (162, 160), (165, 160), (218, -2160), (222, -1440), (224, -1200), (225, 2480), (252, -480), (255, 640), (256, 2240), (260, 420), (261, -1405), (274, -1440)]

def row2251 : Integer.Sparse (Fin 3237) := [(0, 54), (3, -140), (4, 5), (32, 310), (55, 360), (66, 360), (68, 80), (71, 360), (122, 720), (127, 720), (135, 720), (139, 1440), (159, -600), (160, 3280), (218, -480), (222, -120), (224, -240), (225, 1080), (251, -480), (253, -120), (255, 720), (256, 1480), (260, 30), (261, -935), (274, -240)]

def row2252 : Integer.Sparse (Fin 3237) := [(0, 4), (3, -420), (4, 20), (8, -960), (24, -1920), (32, 605), (42, 720), (45, 1440), (64, -720), (66, 880), (68, 800), (71, 640), (97, 720), (99, 1440), (102, 1440), (160, 5680), (162, 3840), (165, 640), (218, -480), (219, -1200), (220, -240), (224, -720), (225, 3120), (255, 320), (256, 640), (261, -875)]

def row2253 : Integer.Sparse (Fin 3237) := [(0, 8), (8, -720), (24, -1920), (32, 155), (59, 720), (60, 1440), (64, -720), (107, 720), (114, 1440), (148, 1440), (160, 6480), (162, 2800), (218, -480), (222, -960), (224, -1920), (225, 3200), (252, -720), (256, 1920), (260, 60), (261, -1045)]

def row2254 : Integer.Sparse (Fin 3237) := [(0, -7), (3, -100), (4, 5), (8, -720), (24, -960), (32, 435), (43, 720), (45, 1440), (66, 480), (68, 800), (106, 1440), (107, 720), (114, 1440), (160, 4560), (162, 3600), (165, 640), (225, 3200), (227, -720), (252, -240), (255, 160), (256, 800), (261, -515)]

def row2255 : Integer.Sparse (Fin 3237) := [(0, -22), (3, -180), (8, -1680), (24, -960), (32, 365), (42, 720), (44, 1440), (64, -240), (66, 720), (68, 320), (71, 320), (99, 1440), (107, 720), (114, 1440), (159, -1920), (160, 4880), (162, 3920), (218, -720), (219, -1920), (220, -720), (224, -480), (225, 2800), (252, -240), (256, 320), (260, 180), (261, -465)]

def row2256 : Integer.Sparse (Fin 3237) := [(0, 6), (3, -260), (4, 15), (32, 225), (66, 1360), (68, 1200), (71, 160), (75, 720), (99, 1440), (106, 720), (109, 1440), (110, 1440), (135, 1440), (160, 2560), (162, 1040), (165, 560), (218, -480), (219, -720), (225, 1600), (252, -960), (253, -240), (255, 720), (256, 800), (261, -140)]

def row2257 : Integer.Sparse (Fin 3237) := [(0, 39), (3, -740), (4, 65), (24, -480), (32, 615), (61, -480), (66, 720), (68, 560), (71, 1120), (108, 720), (112, 1440), (113, 1440), (138, 1440), (159, -1440), (160, 3600), (162, 240), (165, 880), (218, -240), (219, -960), (225, 560), (255, 640), (256, 960), (261, -385), (274, -720)]

def row2258 : Integer.Sparse (Fin 3237) := [(0, 24), (3, -220), (4, 10), (24, -960), (32, 495), (61, -480), (66, 800), (68, 720), (71, 160), (75, 720), (79, 1440), (99, 720), (101, 1440), (106, 1440), (108, 720), (120, 1440), (142, 1440), (159, -480), (160, 4320), (162, 960), (165, 640), (219, -720), (225, 1120), (252, -960), (253, -720), (255, 1280), (256, 2000), (261, -795), (274, -1200)]

def row2259 : Integer.Sparse (Fin 3237) := [(0, 44), (3, -260), (4, 15), (32, 385), (61, -960), (66, 640), (68, 320), (71, 480), (74, 720), (79, 1440), (98, 2160), (102, 1440), (112, 1440), (127, 1440), (160, 4960), (162, 160), (165, 160), (222, -480), (225, 240), (251, -1200), (253, -960), (255, 2160), (256, 2480), (261, -690), (274, -480)]

def row2260 : Integer.Sparse (Fin 3237) := [(0, -1), (3, -420), (4, 35), (8, -480), (24, -1440), (32, 480), (43, 720), (61, -480), (66, 1200), (68, 1200), (71, 240), (106, 720), (107, 1440), (108, 720), (120, 1440), (121, 1440), (135, 1440), (159, -720), (160, 3520), (162, 720), (165, 1120), (218, -240), (219, -480), (222, -240), (225, 880), (227, -240), (252, -480), (255, 880), (256, 1120), (261, -390), (274, -720)]

def row2261 : Integer.Sparse (Fin 3237) := [(0, 23), (3, -210), (4, 10), (24, -600), (32, 310), (61, -240), (66, 280), (68, 120), (71, 360), (79, 360), (89, 360), (101, 720), (109, 360), (112, 720), (113, 360), (115, 720), (138, 360), (160, 1720), (162, 80), (165, 200), (219, -240), (222, -240), (225, 160), (251, -120), (252, -240), (253, -120), (255, 400), (256, 760), (261, -385), (274, -720)]

def row2262 : Integer.Sparse (Fin 3237) := [(0, 21), (3, -88), (4, 4), (32, 170), (61, -96), (66, 80), (68, 32), (71, 192), (79, 144), (89, 144), (102, 288), (127, 288), (160, 880), (165, 80), (251, -96), (253, -48), (255, 288), (256, 432), (261, -255), (270, 288), (272, 288), (273, -96), (274, -96)]

def row2263 : Integer.Sparse (Fin 3237) := [(0, 3), (3, -26), (4, 1), (24, -120), (32, 53), (61, -48), (66, 72), (68, 80), (71, 32), (75, 72), (79, 144), (98, 144), (99, 144), (100, 144), (101, 288), (102, 288), (121, 72), (159, -48), (160, 640), (162, 144), (165, 64), (219, -48), (224, -240), (225, 200), (252, -72), (253, -72), (255, 176), (256, 240), (261, -113)]

def row2264 : Integer.Sparse (Fin 3237) := [(0, 7), (3, -60), (4, 3), (24, -480), (32, 111), (61, -192), (66, 160), (68, 80), (71, 96), (74, 144), (79, 288), (96, 288), (97, 288), (98, 288), (101, 576), (102, 576), (113, 288), (160, 1424), (162, 144), (165, 32), (218, -96), (219, -144), (224, -480), (225, 352), (252, -144), (253, -192), (255, 416), (256, 464), (261, -235), (274, -96)]

def row2265 : Integer.Sparse (Fin 3237) := [(0, 11), (3, -90), (24, -240), (32, 160), (66, 480), (68, 80), (71, 120), (113, 720), (122, 720), (146, 360), (159, -600), (160, 1680), (162, 80), (218, -360), (219, -240), (222, -600), (225, 880), (252, -360), (256, 360), (260, 180), (261, -185), (274, -240)]

def row2266 : Integer.Sparse (Fin 3237) := [(0, 21), (3, -36), (32, 124), (66, 192), (68, 32), (71, 48), (109, 288), (125, 288), (142, 576), (145, 144), (159, -240), (160, 1072), (218, -144), (219, -96), (222, -240), (225, 192), (252, -288), (255, 128), (256, 672), (260, 72), (261, -333), (274, -672)]

def row2267 : Integer.Sparse (Fin 3237) := [(0, -18), (3, -440), (4, 25), (8, -960), (24, -960), (32, 555), (43, 720), (44, 720), (45, 720), (64, -720), (66, 1200), (68, 1040), (71, 560), (98, 720), (101, 720), (102, 720), (106, 1440), (108, 1440), (116, 720), (120, 720), (159, -960), (160, 5200), (162, 3200), (165, 800), (219, -480), (224, -720), (225, 2240), (227, -240), (255, 640), (256, 720), (261, -560)]

def row2268 : Integer.Sparse (Fin 3237) := [(0, 4), (3, -12), (4, 3), (20, -96), (31, 24), (32, 7), (122, 432), (153, -144), (215, -48), (218, -144), (252, -144), (260, 84), (261, -44), (266, -288), (267, -144), (273, -144), (274, -288)]

def row2269 : Integer.Sparse (Fin 3237) := [(0, 6), (3, -112), (4, 6), (31, 24), (32, 119), (66, 144), (68, 32), (71, 288), (153, -144), (159, -288), (160, 240), (162, 32), (215, -48), (218, -144), (219, -144), (225, 96), (260, 108), (261, -53), (266, -288), (273, -288)]

def row2270 : Integer.Sparse (Fin 3237) := [(0, 37), (3, -840), (4, 40), (32, 975), (66, 1760), (68, 800), (71, 1920), (108, 1440), (109, 720), (127, 1440), (159, -4320), (160, 4880), (162, 480), (165, 320), (218, -480), (219, -960), (222, -1440), (224, -480), (225, 960), (251, -1200), (255, 640), (256, 1360), (260, 600), (261, -930), (268, -720), (273, -960), (274, -960)]

def row2271 : Integer.Sparse (Fin 3237) := [(0, -1), (20, -1440), (31, 60), (32, 5), (153, -960), (177, 1440), (195, 2160), (215, -480), (218, -2400), (252, -1440), (261, 110), (263, 2160)]

def row2272 : Integer.Sparse (Fin 3237) := [(0, -2), (3, -80), (20, -480), (24, -1440), (31, 60), (32, 195), (66, 480), (68, 160), (153, -720), (156, -240), (159, -1440), (160, 3040), (162, 480), (191, 1440), (196, 2160), (215, -480), (218, -2160), (219, -1440), (222, -720), (225, 1840), (238, 2160), (252, -1440), (256, 720), (260, 420), (261, -455)]

def row2273 : Integer.Sparse (Fin 3237) := [(0, 8), (3, -12), (4, 3), (20, -96), (31, 12), (32, 25), (96, 432), (128, 432), (150, -432), (153, -144), (198, 432), (215, -96), (218, -288), (233, 432), (244, 288), (250, -144), (252, -624), (260, 48), (261, -30), (266, -48), (267, -144), (273, -144), (274, -576)]

def row2274 : Integer.Sparse (Fin 3237) := [(0, 52), (20, -960), (32, 55), (122, 2160), (128, 2160), (150, -720), (198, 2160), (218, -1440), (252, -3600), (260, 480), (261, -425), (264, 1440), (267, -720), (273, -960), (274, -4080)]

def row2275 : Integer.Sparse (Fin 3237) := [(0, -9), (3, -160), (31, 60), (32, 530), (66, 960), (68, 320), (99, 4320), (153, -720), (154, -240), (159, -2880), (160, 6960), (162, 4560), (181, 2160), (182, 1440), (197, 2160), (215, -480), (218, -2880), (219, -2880), (224, -1440), (225, 3440), (260, 540), (261, -845)]

def row2276 : Integer.Sparse (Fin 3237) := [(0, 101), (3, -20), (20, -480), (24, -1440), (32, 420), (66, 240), (68, 160), (135, 4320), (145, 2160), (159, -240), (160, 8560), (162, 480), (189, 1440), (199, 2160), (218, -1440), (222, -1440), (224, -1440), (225, 2640), (252, -1440), (255, 1760), (256, 3280), (260, 240), (261, -2045), (274, -1440)]

def row2277 : Integer.Sparse (Fin 3237) := [(0, 149), (3, -40), (20, -480), (32, 265), (66, 480), (68, 560), (128, 2160), (138, 4320), (150, -720), (160, 6960), (162, 320), (218, -1440), (222, -1440), (224, -2160), (225, 1200), (252, -3600), (255, 2400), (256, 5280), (260, 240), (261, -2280), (274, -3600)]

def row2278 : Integer.Sparse (Fin 3237) := [(0, 32), (3, -60), (20, -240), (32, 95), (128, 2160), (150, -720), (153, -480), (177, 720), (195, 1080), (198, 2160), (218, -1920), (233, 4320), (252, -2880), (260, 480), (261, -25), (263, 2160), (273, -720), (274, -2160)]

def row2279 : Integer.Sparse (Fin 3237) := [(0, 31), (3, -24), (32, 141), (156, -192), (159, -288), (160, 704), (162, 64), (165, 96), (191, 288), (196, 432), (204, 864), (218, -144), (222, -432), (225, 320), (238, 864), (240, 1728), (256, 384), (260, 180), (261, -354), (273, -288)]

def row2280 : Integer.Sparse (Fin 3237) := [(0, 23), (32, 210), (68, 240), (99, 1080), (102, 2160), (154, -480), (159, -720), (160, 3840), (162, 960), (165, 240), (181, 2160), (182, 720), (193, 4320), (197, 1080), (198, 2160), (218, -1080), (224, -1800), (225, 1840), (255, 480), (256, 1200), (261, -885)]

def row2281 : Integer.Sparse (Fin 3237) := [(0, 3), (3, -60), (24, -480), (31, 60), (32, 165), (66, 320), (146, 1440), (153, -480), (156, -480), (159, -480), (160, 2080), (178, 1440), (196, 1440), (217, -480), (218, -1680), (222, -1440), (224, -960), (225, 1120), (238, 1440), (252, -1200), (256, 640), (260, 360), (261, -290), (263, 720)]

def row2282 : Integer.Sparse (Fin 3237) := [(0, 17), (3, -120), (31, 60), (32, 260), (66, 640), (145, 2880), (153, -240), (154, -720), (156, -480), (159, -960), (160, 4720), (162, 560), (181, 2160), (197, 720), (218, -2880), (222, -1920), (224, -1920), (225, 2000), (238, 1440), (256, 1120), (260, 540), (261, -725)]

def row2283 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -5), (21, -120), (24, -360), (32, 40), (66, 60), (99, 180), (129, 360), (135, 720), (148, 180), (160, 1160), (162, 80), (218, -120), (219, -60), (225, 780), (252, -660), (255, 200), (256, 440), (261, -160)]

def row2284 : Integer.Sparse (Fin 3237) := [(0, 47), (3, -120), (4, 5), (24, -480), (32, 350), (66, 240), (68, 160), (71, 160), (109, 720), (135, 720), (145, 1440), (146, 720), (159, -2880), (160, 4640), (165, 240), (207, 1440), (210, 1440), (218, -480), (219, -480), (222, -960), (225, 1120), (241, 1440), (251, -1200), (252, -240), (255, 720), (256, 2480), (260, 360), (261, -1150), (268, -240), (274, -1680)]

def row2285 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -4), (24, -96), (32, 31), (66, 48), (68, 32), (131, 144), (145, 288), (146, 144), (148, 432), (159, -48), (160, 1088), (162, 144), (199, 288), (202, 288), (218, -240), (222, -288), (224, -384), (225, 464), (252, -144), (255, 32), (256, 432), (260, 36), (261, -206)]

def row2286 : Integer.Sparse (Fin 3237) := [(0, 32), (24, -1440), (29, 160), (32, 235), (106, 720), (132, 720), (135, 2880), (136, 1440), (148, 1440), (160, 4960), (162, 1440), (225, 3520), (252, -1920), (255, 400), (256, 1760), (261, -825)]

def row2287 : Integer.Sparse (Fin 3237) := [(0, 29), (24, -360), (29, 160), (32, 105), (115, 360), (133, 180), (138, 360), (139, 360), (140, 360), (141, 360), (160, 1560), (162, 440), (225, 440), (255, 320), (256, 760), (261, -340), (274, -540)]

def row2288 : Integer.Sparse (Fin 3237) := [(0, 116), (3, -60), (32, 325), (66, 240), (68, 160), (71, 160), (109, 720), (127, 1440), (135, 1440), (142, 1440), (145, 720), (147, 1440), (159, -1680), (160, 3200), (162, 160), (211, 1440), (225, 800), (235, 1440), (251, -240), (255, 480), (256, 2000), (261, -1215), (268, -720), (274, -2880)]

def row2289 : Integer.Sparse (Fin 3237) := [(0, 29), (21, -720), (24, -2400), (29, 320), (32, 335), (99, 720), (101, 1440), (129, 720), (130, 1440), (133, 720), (135, 1440), (136, 1440), (142, 1440), (148, 1440), (160, 4880), (162, 1200), (219, -720), (225, 2080), (252, -2880), (255, 800), (256, 2000), (261, -1090), (274, -2160)]

def row2290 : Integer.Sparse (Fin 3237) := [(0, 21), (3, -220), (21, -480), (24, -2400), (31, 60), (32, 610), (66, 320), (71, 640), (101, 2880), (109, 1440), (115, 2880), (129, 1440), (153, -240), (154, -240), (156, -480), (159, -2880), (160, 5520), (162, 1360), (181, 720), (191, 1440), (192, 1440), (196, 1440), (217, -480), (218, -720), (222, -1440), (224, -960), (225, 2160), (251, -2400), (252, -960), (256, 2560), (260, 360), (261, -1115), (268, -480), (274, -1920)]

def row2291 : Integer.Sparse (Fin 3237) := [(0, 37), (24, -96), (29, 32), (32, 139), (133, 288), (135, 288), (136, 288), (139, 576), (142, 576), (148, 144), (160, 1216), (162, 16), (225, 384), (252, -144), (255, 224), (256, 704), (261, -406), (274, -576)]

def row2292 : Integer.Sparse (Fin 3237) := [(0, 126), (3, -20), (24, -480), (32, 305), (66, 240), (68, 160), (131, 720), (132, 1440), (135, 2160), (138, 4320), (145, 720), (146, 1440), (159, -240), (160, 7920), (207, 1440), (210, 1440), (218, -1200), (222, -1440), (224, -1920), (225, 2320), (252, -2640), (255, 2000), (256, 5120), (260, 180), (261, -2265), (274, -1680)]

def row2293 : Integer.Sparse (Fin 3237) := [(0, 39), (3, -100), (4, 5), (21, -480), (24, -2400), (32, 670), (66, 160), (68, 240), (71, 160), (99, 720), (101, 1440), (109, 720), (115, 4320), (129, 1440), (145, 720), (159, -2400), (160, 8160), (162, 3440), (165, 240), (188, 1440), (189, 1440), (199, 1440), (218, -240), (219, -720), (222, -480), (224, -720), (225, 3200), (251, -1200), (252, -1200), (255, 320), (256, 2720), (260, 180), (261, -1590), (268, -240), (274, -1920)]

def row2294 : Integer.Sparse (Fin 3237) := [(0, 102), (24, -720), (29, 80), (32, 365), (132, 360), (133, 720), (138, 720), (139, 2160), (141, 720), (142, 720), (160, 3440), (162, 240), (225, 1280), (252, -480), (255, 320), (256, 2120), (261, -1245), (274, -1440)]

def row2295 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -28), (4, 2), (24, -384), (32, 78), (66, 48), (68, 160), (71, 32), (97, 144), (101, 576), (109, 144), (115, 576), (159, -384), (160, 1568), (162, 608), (165, 64), (211, 288), (218, -48), (219, -432), (222, -96), (224, -144), (225, 608), (235, 288), (245, 288), (251, -336), (252, -192), (255, 224), (256, 592), (260, 36), (261, -341), (268, -48), (274, -288)]

def row2296 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -44), (4, 4), (24, -240), (31, 12), (32, 90), (66, 64), (68, 96), (71, 64), (101, 576), (109, 144), (112, 288), (115, 576), (150, -96), (153, -48), (156, -96), (159, -288), (160, 1280), (162, 288), (165, 64), (178, 144), (193, 288), (198, 288), (211, 288), (217, -144), (218, -48), (219, -96), (222, -288), (224, -192), (225, 400), (235, 288), (244, 288), (245, 288), (251, -240), (252, -144), (255, 224), (256, 528), (260, 48), (261, -307), (267, -96), (268, -48), (274, -288)]

def row2297 : Integer.Sparse (Fin 3237) := [(0, 53), (3, -160), (21, -480), (24, -1200), (31, 60), (32, 470), (66, 480), (71, 320), (113, 1440), (138, 1440), (146, 2880), (154, -720), (156, -720), (159, -1920), (160, 4400), (178, 1440), (192, 720), (196, 720), (218, -1680), (219, -960), (222, -1680), (224, -960), (225, 1520), (239, 1440), (252, -3360), (255, 320), (256, 2400), (260, 420), (261, -1175), (268, -480), (274, -2880)]

def row2298 : Integer.Sparse (Fin 3237) := [(0, 54), (3, -100), (4, 5), (21, -480), (24, -1200), (32, 420), (66, 320), (68, 240), (71, 80), (113, 720), (121, 720), (135, 720), (138, 720), (145, 720), (146, 1440), (148, 1440), (159, -2160), (160, 6320), (162, 560), (165, 240), (188, 720), (199, 720), (202, 1440), (218, -960), (219, -960), (222, -480), (224, -480), (225, 2400), (241, 720), (251, -480), (252, -3360), (255, 720), (256, 3040), (260, 240), (261, -1555), (268, -240), (274, -2640)]

def row2299 : Integer.Sparse (Fin 3237) := [(0, 2), (3, -72), (4, 3), (21, -96), (24, -384), (29, 112), (31, 12), (32, 136), (66, 240), (68, 80), (71, 112), (98, 288), (127, 288), (130, 288), (154, -48), (156, -144), (159, -288), (160, 1264), (162, 128), (165, 32), (178, 288), (179, 144), (192, 144), (193, 144), (196, 144), (217, -48), (218, -48), (222, -192), (224, -144), (225, 128), (252, -96), (255, 528), (256, 480), (260, 36), (261, -173), (266, -48), (268, -96), (274, -192)]

def row2300 : Integer.Sparse (Fin 3237) := [(0, 103), (3, -40), (4, 5), (24, -960), (29, 720), (32, 560), (68, 160), (140, 1440), (160, 7920), (162, 480), (165, 160), (180, 720), (199, 720), (202, 1440), (209, 1440), (224, -480), (225, 720), (255, 3920), (256, 3840), (261, -1580), (272, 1440), (274, -480)]

def row2301 : Integer.Sparse (Fin 3237) := [(0, 71), (3, -80), (4, 10), (24, -1440), (29, 720), (32, 410), (66, 160), (68, 320), (71, 80), (98, 1440), (102, 720), (140, 1440), (159, -240), (160, 8000), (162, 560), (165, 80), (206, 720), (209, 1440), (210, 720), (224, -720), (225, 560), (235, 720), (251, -480), (255, 4080), (256, 3920), (261, -1455), (272, 720), (274, -960)]

def row2302 : Integer.Sparse (Fin 3237) := [(0, 1), (1, 284), (2, -11), (3, 276), (4, -54), (32, -91), (34, -96), (35, -32), (36, -48), (37, -192), (66, -48), (68, -96), (70, -144), (71, -96), (160, -48), (164, -192), (165, -192), (221, 144), (261, -49), (265, 288)]

def row2303 : Integer.Sparse (Fin 3237) := [(0, 9), (1, 740), (2, -20), (3, 1520), (4, -180), (32, -530), (33, 720), (34, -2400), (35, -1280), (36, -240), (37, -3840), (66, -1920), (68, -640), (71, -1920), (160, -480), (261, -255)]

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

def row2304 : Integer.Sparse (Fin 3237) := [(1, 28), (2, -1), (3, 76), (4, -12), (32, -28), (34, -96), (35, -64), (36, -48), (66, -144), (68, -224), (70, -48), (160, -192), (164, -96), (165, -144), (221, 144), (253, 144), (254, -48), (255, -96), (256, -48), (261, 3)]

def row2305 : Integer.Sparse (Fin 3237) := [(0, -1), (1, 100), (2, -5), (3, 420), (4, -75), (32, -25), (36, -80), (68, -1440), (160, -1440), (165, -1280), (223, 720), (224, 720), (226, 480), (253, 1440), (254, -480), (255, -960), (256, -480), (261, 70)]

def row2306 : Integer.Sparse (Fin 3237) := [(0, 6), (1, 120), (2, -5), (3, 480), (4, -90), (32, -260), (34, -240), (35, -160), (36, -320), (66, -480), (68, -1680), (69, -1280), (70, -240), (155, 720), (160, -1440), (162, -2160), (163, -1200), (164, -480), (165, -1440), (216, 480), (219, 720), (220, 1440), (221, 720), (225, -480), (227, 1440), (261, -105)]

def row2307 : Integer.Sparse (Fin 3237) := [(0, 1), (1, 180), (2, -5), (3, 560), (4, -60), (32, -270), (34, -480), (35, -160), (37, -960), (65, 720), (66, -720), (67, 480), (68, -160), (70, -80), (71, -800), (159, 720), (160, -480), (165, -240), (256, -80), (261, -80)]

def row2308 : Integer.Sparse (Fin 3237) := [(0, 6), (1, 300), (2, -10), (3, 440), (4, -90), (32, -235), (34, -80), (36, -80), (37, -320), (68, -480), (69, -320), (70, -160), (71, -320), (155, 240), (160, -400), (162, -320), (163, -400), (164, -160), (165, -880), (227, 960), (249, 960), (251, 480), (253, 240), (254, -80), (255, -160), (256, -80), (261, -185), (265, 480)]

def row2309 : Integer.Sparse (Fin 3237) := [(0, -1), (1, 100), (2, -5), (3, 320), (4, -35), (31, -60), (32, -190), (34, -320), (37, -160), (65, 480), (66, -480), (68, -320), (70, -160), (71, -320), (153, 240), (156, 480), (158, 480), (159, 480), (160, -640), (164, -160), (165, -480), (255, -160), (256, -160), (260, -60), (261, -15)]

def row2310 : Integer.Sparse (Fin 3237) := [(0, 1), (1, 60), (2, -5), (3, 420), (4, -25), (31, -120), (32, -15), (36, -80), (68, -1120), (158, 480), (160, -1120), (164, -160), (165, -320), (223, 240), (224, 240), (254, -320), (255, -800), (256, -320), (260, -120), (261, 60), (268, 960)]

def row2311 : Integer.Sparse (Fin 3237) := [(0, 7), (1, 80), (2, -5), (3, 460), (4, -60), (31, -60), (32, -175), (34, -160), (35, -160), (36, -80), (37, -80), (66, -400), (67, 480), (68, -720), (69, -320), (70, -160), (71, -160), (154, 480), (155, 240), (156, 240), (159, 480), (160, -1040), (161, 480), (162, -1360), (163, -400), (164, -160), (165, -960), (219, 240), (225, -320), (261, -55)]

def row2312 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 24), (4, -3), (32, -38), (68, -192), (157, 144), (158, 576), (159, 576), (160, -640), (161, 384), (162, -256), (163, -48), (164, -64), (165, -192), (224, 576), (225, -192), (255, -192), (256, -192), (260, -36), (261, 64)]

def row2313 : Integer.Sparse (Fin 3237) := [(0, 3), (1, 160), (2, -10), (3, 700), (4, -60), (31, -180), (32, -200), (34, -80), (37, -400), (65, 240), (66, -80), (70, -80), (71, -480), (156, 240), (160, -400), (165, -480), (260, -180), (261, -45), (266, 480), (267, 480)]

def row2314 : Integer.Sparse (Fin 3237) := [(0, 8), (1, 60), (2, -5), (3, 420), (4, -25), (31, -120), (32, -40), (36, -80), (68, -880), (69, -160), (160, -560), (161, 480), (162, -720), (163, -160), (164, -160), (165, -560), (224, 240), (225, -80), (226, 240), (254, -160), (255, -320), (261, -40), (267, 480)]

def row2315 : Integer.Sparse (Fin 3237) := [(0, 6), (1, 140), (2, -10), (3, 480), (4, -30), (31, -180), (32, -15), (35, -160), (36, -80), (37, -240), (66, -160), (67, 240), (68, -960), (69, -160), (70, -80), (71, -160), (160, -480), (162, -320), (165, -160), (217, 480), (249, 240), (251, 240), (254, -160), (255, -480), (256, -80), (261, -5), (266, 240), (268, 240)]

def row2316 : Integer.Sparse (Fin 3237) := [(0, 1), (1, 36), (3, 148), (4, -15), (5, 144), (6, -32), (32, -51), (34, -288), (35, -112), (37, -432), (66, -144), (68, -80), (71, -192), (160, -48), (164, -48), (165, -96), (261, -33)]

def row2317 : Integer.Sparse (Fin 3237) := [(0, 2), (1, 50), (3, 170), (4, -25), (6, -80), (7, 360), (9, 240), (10, -80), (32, -10), (34, -360), (35, -320), (37, -240), (66, -360), (68, -560), (160, -280), (162, -120), (164, -40), (165, -240), (219, 360), (255, -120), (261, -15)]

def row2318 : Integer.Sparse (Fin 3237) := [(0, 9), (1, 80), (3, 840), (4, -100), (5, 240), (7, 240), (8, 480), (11, 960), (32, -300), (34, -560), (35, -80), (37, -1200), (66, -320), (68, -400), (71, -960), (159, 240), (160, -480), (162, -320), (163, -160), (164, -160), (165, -880), (251, 480), (255, -80), (256, -80), (261, -225)]

def row2319 : Integer.Sparse (Fin 3237) := [(0, 3), (1, 40), (3, 260), (4, -25), (5, 240), (6, -80), (27, -160), (32, -80), (34, -400), (35, -240), (37, -320), (61, 240), (66, -640), (68, -720), (71, -320), (160, -560), (164, -80), (165, -240), (255, -240), (256, -80), (261, -30)]

def row2320 : Integer.Sparse (Fin 3237) := [(1, 4), (4, 1), (6, -32), (10, -64), (13, 96), (17, -32), (20, 144), (32, 12), (35, -64), (68, -96), (162, -160), (215, 144), (261, -1)]

def row2321 : Integer.Sparse (Fin 3237) := [(0, 7), (1, 20), (3, 140), (4, -35), (6, -160), (10, -160), (19, 480), (27, -480), (29, -480), (32, 40), (35, -240), (37, -80), (66, -480), (68, -1360), (160, -1280), (162, -640), (217, 720), (224, 720), (225, -240), (255, -800), (261, 60)]

def row2322 : Integer.Sparse (Fin 3237) := [(0, -2), (1, 20), (3, 220), (4, -45), (6, -160), (14, 480), (21, 1440), (27, -960), (29, -1280), (32, -60), (34, -80), (35, -240), (66, -960), (68, -2000), (154, 720), (160, -4080), (162, -1200), (165, -480), (224, 720), (255, -2880), (256, -960), (261, 315)]

def row2323 : Integer.Sparse (Fin 3237) := [(0, 3), (1, 80), (3, 200), (4, -40), (6, -160), (7, 480), (14, 480), (27, -320), (29, -160), (32, 35), (34, -160), (35, -320), (37, -160), (66, -480), (68, -960), (153, 240), (160, -480), (162, -160), (164, -160), (215, 240), (217, 480), (219, 480), (255, -480), (261, 20)]

def row2324 : Integer.Sparse (Fin 3237) := [(0, 6), (1, 60), (3, 420), (4, -70), (6, -160), (9, 240), (10, -400), (11, 480), (19, 480), (21, 240), (27, -160), (29, -400), (32, -125), (34, -240), (35, -160), (37, -160), (66, -320), (68, -1200), (71, -160), (154, 480), (156, 240), (160, -1360), (162, -960), (163, -320), (164, -240), (165, -1040), (217, 240), (251, 480), (255, -640), (256, -160), (261, -65)]

def row2325 : Integer.Sparse (Fin 3237) := [(0, 9), (1, 100), (3, 460), (4, -85), (7, 240), (32, -85), (34, -320), (35, -80), (37, -480), (66, -640), (68, -560), (71, -480), (150, 480), (153, 480), (156, 240), (159, 240), (160, -800), (164, -80), (165, -400), (217, 240), (255, -400), (256, -80), (261, -45), (266, 480)]

def row2326 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 16), (4, -2), (5, 48), (8, 96), (9, 48), (10, -16), (12, -96), (15, 48), (21, 96), (24, 48), (29, -32), (32, -12), (34, -32), (37, -16), (68, -32), (154, 96), (160, -112), (162, -144), (163, -32), (164, -16), (165, -96), (217, 48), (224, 96), (225, -32), (255, -16), (261, -3)]

def row2327 : Integer.Sparse (Fin 3237) := [(0, 7), (3, 180), (4, -15), (5, 240), (6, -80), (7, 240), (14, 240), (21, 480), (24, 240), (27, -320), (29, -240), (32, -25), (34, -80), (35, -80), (61, 480), (66, -720), (68, -960), (71, -160), (149, -480), (150, 480), (153, 240), (154, 240), (159, 240), (160, -1920), (162, -80), (164, -80), (165, -240), (218, 240), (219, 240), (224, 240), (225, -160), (252, 480), (255, -1120), (256, -560), (261, 95)]

def row2328 : Integer.Sparse (Fin 3237) := [(0, 8), (3, 680), (4, -55), (24, 480), (25, 480), (27, -800), (29, -320), (30, -160), (32, -340), (61, 1920), (62, 480), (63, 480), (64, 240), (66, -1920), (68, -2640), (69, -80), (71, -800), (160, -3120), (162, -160), (165, -800), (224, 240), (225, -80), (253, 480), (254, -160), (255, -1760), (256, -800), (261, 35)]

def row2329 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 52), (4, -8), (8, 240), (10, -64), (22, 48), (24, 96), (29, -32), (30, -16), (32, -27), (66, -16), (68, -144), (69, -32), (71, -16), (152, 96), (160, -224), (162, -304), (163, -96), (165, -176), (214, 96), (219, 48), (220, 24), (225, -88), (227, 48), (253, 48), (254, -16), (255, -32), (256, -16), (261, -12)]

def row2330 : Integer.Sparse (Fin 3237) := [(0, 6), (3, 440), (4, -35), (10, -160), (25, 720), (27, -960), (29, -480), (30, -240), (32, -180), (61, 1440), (66, -1680), (68, -2800), (71, -480), (160, -2880), (162, -240), (165, -720), (253, 720), (254, -240), (255, -1920), (256, -720), (261, 65)]

def row2331 : Integer.Sparse (Fin 3237) := [(0, 1), (3, 108), (4, -14), (8, 96), (10, -64), (22, 48), (24, 96), (27, -64), (28, 96), (29, -64), (30, -48), (32, -39), (61, 192), (66, -192), (68, -544), (71, -64), (152, 192), (160, -576), (162, -112), (163, -16), (165, -256), (214, 96), (219, 48), (225, -32), (251, 96), (253, 480), (254, -128), (255, -352), (256, -160), (261, 6)]

def row2332 : Integer.Sparse (Fin 3237) := [(0, 7), (10, -240), (15, 720), (17, -80), (24, 1440), (29, -480), (32, -120), (151, 1440), (157, 720), (159, 720), (160, -1920), (162, -2000), (163, -240), (165, -240), (225, -960), (255, -240), (256, -240), (261, 105)]

def row2333 : Integer.Sparse (Fin 3237) := [(0, 14), (3, 340), (4, -65), (10, -160), (24, 240), (29, -160), (32, -80), (62, 240), (68, -560), (69, -80), (150, 480), (151, 480), (160, -1200), (162, -1280), (163, -320), (165, -1120), (225, -160), (255, -240), (261, -65), (267, 480)]

def row2334 : Integer.Sparse (Fin 3237) := [(0, 7), (3, 200), (4, -30), (20, 240), (24, 120), (32, -25), (62, 120), (68, -440), (69, -40), (150, 240), (160, -480), (162, -480), (163, -40), (165, -440), (214, 120), (224, 120), (225, -40), (254, -40), (255, -200), (261, -10), (267, 240)]

def row2335 : Integer.Sparse (Fin 3237) := [(0, -5), (1, -120), (3, -556), (4, 42), (5, -576), (32, 228), (33, -144), (34, 848), (35, 272), (37, 1664), (38, 144), (39, 576), (40, 576), (66, 656), (68, 224), (71, 928), (160, 224), (165, 192), (221, -144), (261, 131), (265, -288)]

def row2336 : Integer.Sparse (Fin 3237) := [(0, -23), (1, -40), (3, -420), (4, 30), (32, 220), (33, -240), (34, 400), (35, 240), (37, 160), (52, 1440), (53, 2160), (55, 2880), (59, 720), (64, -240), (66, 1520), (68, 800), (71, 640), (159, -1440), (160, 3200), (162, 160), (218, -1920), (219, -1680), (222, -960), (224, -1440), (225, 560), (253, -960), (255, 320), (260, 420), (261, -195)]

def row2337 : Integer.Sparse (Fin 3237) := [(0, -19), (1, -40), (3, -740), (4, 20), (5, -960), (8, -1920), (32, 430), (33, -240), (34, 720), (35, 400), (37, 320), (38, 720), (39, 1440), (42, 720), (43, 1440), (44, 1440), (64, -720), (66, 2800), (68, 2240), (71, 1280), (159, -1920), (160, 3200), (162, 960), (165, 640), (218, -240), (219, -960), (220, -720), (221, -720), (222, -480), (225, 720), (260, 180), (261, -115)]

def row2338 : Integer.Sparse (Fin 3237) := [(0, -3), (1, -32), (3, -208), (4, 16), (5, -96), (8, -96), (32, 126), (33, -48), (34, 144), (35, 16), (37, 480), (39, 144), (41, 144), (44, 288), (45, 144), (49, 288), (50, 288), (56, 288), (64, -96), (66, 304), (68, 80), (71, 352), (159, -144), (160, 176), (162, 16), (165, 48), (219, -48), (221, -48), (222, -96), (224, -48), (225, 32), (227, -96), (251, -192), (253, -96), (255, 32), (256, 48), (260, 24), (261, 41), (265, -48), (273, -48)]

def row2339 : Integer.Sparse (Fin 3237) := [(0, -5), (1, -24), (3, -360), (4, 26), (5, -96), (32, 210), (34, 208), (35, 80), (37, 320), (40, 288), (61, -192), (66, 352), (68, 144), (71, 576), (85, 144), (88, 288), (89, 288), (91, 288), (159, -144), (160, 336), (165, 288), (256, 16), (261, 101), (265, -144)]

def row2340 : Integer.Sparse (Fin 3237) := [(0, -13), (1, -160), (3, -580), (4, 70), (5, -480), (8, -480), (32, 155), (33, -240), (34, 1600), (35, 960), (37, 640), (38, 720), (41, 720), (42, 1440), (43, 720), (47, 1440), (48, 1440), (55, 1440), (64, -480), (66, 1840), (68, 1520), (71, 960), (159, -480), (160, 2000), (162, 80), (165, 160), (218, -720), (219, -1200), (220, -480), (221, -480), (222, -240), (224, -240), (225, 160), (253, -480), (255, 160), (260, 120), (261, -30)]

def row2341 : Integer.Sparse (Fin 3237) := [(0, -11), (1, -80), (3, -900), (4, 70), (5, -1440), (32, 605), (33, -720), (34, 640), (35, 320), (37, 640), (38, 720), (39, 1440), (43, 1440), (61, -960), (66, 2400), (68, 2320), (71, 720), (75, 720), (79, 1440), (85, 2160), (91, 1440), (159, -480), (160, 3120), (162, 320), (165, 1920), (221, -240), (222, -240), (225, 160), (227, -480), (253, -720), (255, 480), (256, 400), (261, 10), (265, -720)]

def row2342 : Integer.Sparse (Fin 3237) := [(0, -28), (1, -120), (3, -1660), (4, 105), (5, -480), (8, -1200), (32, 840), (34, 1040), (35, 400), (37, 1600), (40, 1440), (47, 1440), (48, 720), (49, 1440), (51, 2880), (55, 720), (66, 1920), (68, 800), (71, 2880), (159, -1680), (160, 1760), (162, 320), (165, 640), (221, -240), (227, -960), (251, -1440), (253, -240), (255, 160), (256, 400), (261, 415), (265, -480)]

def row2343 : Integer.Sparse (Fin 3237) := [(0, -27), (1, -160), (3, -2280), (4, 225), (5, -480), (32, 1085), (33, -240), (34, 720), (35, 80), (37, 2400), (39, 720), (66, 2320), (68, 880), (71, 3040), (79, 1440), (85, 720), (88, 1440), (91, 1440), (159, -720), (160, 1600), (165, 1280), (253, -480), (255, 160), (256, 80), (261, 555), (265, -480)]

def row2344 : Integer.Sparse (Fin 3237) := [(0, -9), (1, -40), (3, -180), (4, 20), (5, -480), (24, -480), (32, 95), (34, 160), (35, 160), (61, -960), (66, 480), (68, 320), (85, 1440), (104, 1440), (108, 1440), (153, -240), (160, 800), (162, 160), (165, 320), (215, -240), (218, -240), (225, 160), (261, 20), (265, -480), (274, -480)]

def row2345 : Integer.Sparse (Fin 3237) := [(0, -4), (1, -40), (3, -380), (4, 45), (5, -480), (32, 20), (33, -240), (34, 240), (35, 80), (37, 160), (53, 720), (66, 2560), (68, 1440), (71, 480), (103, 1440), (109, 2880), (131, 720), (153, -480), (160, 2400), (162, 160), (165, 320), (217, -480), (218, -480), (219, -1200), (222, -480), (225, 320), (252, -1200), (253, -960), (255, 1120), (256, 640), (261, 15)]

def row2346 : Integer.Sparse (Fin 3237) := [(0, -3), (1, -8), (3, -136), (4, 11), (5, -96), (24, -768), (32, 172), (33, -48), (34, 48), (35, 16), (37, 32), (53, 144), (61, -576), (66, 352), (68, 208), (71, 224), (104, 288), (113, 576), (121, 288), (154, -96), (156, -96), (160, 1232), (162, 160), (165, 224), (218, -144), (219, -240), (222, -96), (224, -48), (225, 256), (253, -192), (255, 256), (256, 224), (261, -76)]

def row2347 : Integer.Sparse (Fin 3237) := [(0, -19), (1, -160), (3, -1260), (4, 220), (5, -480), (32, 440), (33, -240), (34, 560), (35, 400), (37, 160), (53, 720), (66, 1760), (68, 2720), (71, 320), (85, 1440), (103, 1440), (120, 2880), (154, -960), (156, -480), (159, -480), (160, 3680), (162, 2080), (165, 3520), (218, -240), (219, -1200), (225, 400), (253, -960), (255, 480), (256, 160), (261, -5), (265, -480)]

def row2348 : Integer.Sparse (Fin 3237) := [(0, -33), (1, -120), (3, -1360), (4, 170), (5, -480), (8, -1200), (32, 985), (34, 560), (35, 400), (37, 160), (48, 720), (66, 1680), (68, 2800), (71, 960), (91, 1440), (95, 1440), (110, 1440), (116, 2880), (154, -1440), (156, -480), (159, -480), (160, 5680), (162, 4720), (165, 3520), (218, -720), (219, -240), (221, -240), (225, 1840), (227, -960), (261, 100), (265, -480)]

def row2349 : Integer.Sparse (Fin 3237) := [(0, -19), (1, -40), (3, -360), (4, 35), (5, -480), (8, -480), (32, 170), (33, -240), (34, 240), (37, 240), (52, 720), (64, -480), (66, 1760), (68, 720), (71, 800), (95, 1440), (122, 1440), (153, -480), (159, -1200), (160, 2400), (162, 880), (165, 160), (218, -240), (224, -1200), (225, 960), (253, -480), (255, 320), (260, 360), (261, 50), (266, -480)]

def row2350 : Integer.Sparse (Fin 3237) := [(0, -3), (1, -40), (3, -36), (4, 16), (32, 7), (33, -48), (34, 160), (35, 64), (37, 96), (41, 144), (52, 144), (64, -48), (66, 448), (68, 208), (71, 96), (96, 288), (153, -240), (159, -48), (160, 368), (162, 64), (215, -96), (217, -48), (218, -144), (219, -48), (221, -48), (224, -240), (225, 80), (253, -288), (255, 96), (260, 36), (261, 14), (266, -96)]

def row2351 : Integer.Sparse (Fin 3237) := [(0, 1), (1, -20), (3, -220), (4, 15), (20, -480), (31, 240), (32, 200), (34, 240), (35, 160), (65, -240), (66, 960), (68, 320), (146, 2160), (153, -1440), (156, -1440), (159, -720), (160, 2000), (162, 160), (201, 1440), (215, -480), (217, -1440), (218, -2160), (222, -2400), (224, -1440), (225, 720), (236, 2160), (252, -720), (256, 560), (260, 600), (261, -320)]

def row2352 : Integer.Sparse (Fin 3237) := [(0, 54), (3, -940), (4, 45), (32, 935), (55, 2160), (66, 1920), (68, 800), (71, 1920), (109, 4320), (127, 4320), (135, 2160), (159, -3600), (160, 4320), (162, 160), (225, 240), (230, 1440), (251, -1440), (253, -240), (255, 1200), (256, 2000), (261, -660), (268, -2400), (274, -3600)]

def row2353 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -560), (4, 30), (8, -720), (32, 385), (42, 1080), (45, 2160), (64, -1080), (66, 1440), (68, 1120), (71, 960), (84, 2160), (99, 1080), (102, 2160), (160, 2880), (162, 720), (165, 240), (172, 720), (175, 4320), (220, -120), (223, -480), (224, -1080), (225, 520), (253, -720), (254, 240), (255, 960), (256, 720), (261, -190)]

def row2354 : Integer.Sparse (Fin 3237) := [(0, 9), (1, -20), (3, -680), (4, 120), (24, -2880), (32, 170), (34, 240), (35, 160), (62, -2160), (66, 960), (68, 2080), (73, 4320), (97, 2160), (102, 4320), (160, 2880), (165, 1440), (166, 2160), (214, -1440), (216, -240), (219, -720), (224, -2160), (225, 240), (226, -960), (242, 4320), (246, 1440), (248, 8640), (253, -1440), (254, 480), (255, 960), (256, 960), (261, -315)]

def row2355 : Integer.Sparse (Fin 3237) := [(0, -29), (3, -340), (23, -480), (24, -480), (32, 485), (57, 1440), (58, 1440), (59, 720), (64, -240), (66, 1840), (68, 160), (71, 160), (107, 720), (143, 2880), (157, -240), (159, -2880), (160, 3920), (162, 320), (218, -3360), (219, -1200), (222, -2400), (224, -2400), (225, 1200), (252, -480), (255, 160), (260, 1020), (261, -490)]

def row2356 : Integer.Sparse (Fin 3237) := [(0, -12), (1, -20), (3, -260), (4, 5), (31, 180), (32, 300), (34, 240), (35, 160), (53, 720), (59, 1440), (64, -480), (65, -240), (66, 1200), (68, 320), (71, 80), (131, 720), (145, 1440), (153, -240), (154, -2160), (156, -1440), (159, -480), (160, 3440), (162, 320), (165, 160), (183, 1440), (200, 1440), (217, -480), (218, -3600), (222, -3120), (223, -240), (224, -3360), (225, 1040), (236, 720), (255, 160), (256, 640), (260, 780), (261, -405)]

def row2357 : Integer.Sparse (Fin 3237) := [(0, 29), (1, -20), (3, -420), (4, 30), (24, -960), (31, 180), (32, 480), (34, 80), (37, 320), (52, 720), (57, 1440), (62, -480), (65, -240), (66, 240), (71, 800), (122, 720), (125, 1440), (147, 1440), (153, -240), (156, -1680), (159, -720), (160, 1280), (165, 80), (217, -960), (218, -480), (222, -2880), (224, -1920), (225, 320), (226, -240), (236, 720), (256, 800), (259, 1440), (260, 1140), (261, -515), (262, 1440), (266, -1440), (267, -720), (273, -1680), (274, -960)]

def row2358 : Integer.Sparse (Fin 3237) := [(0, -1), (1, -20), (3, -660), (4, 40), (11, -960), (32, 555), (34, 240), (35, 160), (37, 320), (47, 720), (55, 1440), (66, 1040), (67, -720), (68, 480), (71, 1440), (91, 1440), (109, 720), (127, 1440), (142, 1440), (159, -3360), (160, 2800), (165, 480), (228, 1440), (229, 1440), (249, -240), (251, -1680), (253, -480), (255, 640), (256, 960), (261, -80), (268, -720), (274, -960)]

def row2359 : Integer.Sparse (Fin 3237) := [(0, 9), (1, -20), (3, -740), (4, 80), (7, -960), (24, -960), (32, 515), (34, 80), (37, 640), (41, 720), (54, 1440), (65, -720), (66, 400), (71, 1600), (88, 1440), (139, 2880), (159, -2880), (160, 1040), (165, 160), (214, -480), (216, -240), (218, -240), (219, -1440), (225, 400), (231, 2880), (232, 2880), (256, 320), (260, 300), (261, -110), (273, -480)]

def row2360 : Integer.Sparse (Fin 3237) := [(0, -13), (1, -20), (3, -660), (4, 35), (21, -2400), (24, -960), (31, 180), (32, 660), (34, 240), (35, 160), (53, 720), (58, 1440), (63, -480), (66, 1840), (67, -240), (68, 1040), (71, 720), (109, 720), (113, 4320), (121, 1440), (146, 1440), (153, -240), (154, -2160), (156, -1440), (159, -4080), (160, 4800), (162, 720), (165, 640), (183, 720), (187, 1440), (201, 1440), (217, -480), (218, -2160), (219, -3120), (222, -1200), (223, -240), (224, -960), (225, 1440), (251, -1200), (252, -2400), (255, 320), (256, 960), (260, 480), (261, -630), (268, -1680), (274, -1920)]

def row2361 : Integer.Sparse (Fin 3237) := [(0, 18), (1, -10), (3, -510), (4, 35), (31, 90), (32, 425), (34, 40), (37, 160), (52, 360), (64, -240), (66, 1040), (67, -120), (68, 680), (69, 80), (71, 960), (108, 720), (127, 1440), (147, 720), (153, -120), (156, -840), (159, -1080), (160, 2760), (162, 480), (165, 80), (183, 360), (217, -480), (222, -960), (224, -840), (225, 520), (226, -120), (255, 560), (256, 720), (258, 720), (259, 720), (260, 270), (261, -520), (266, -720), (268, -480), (273, -480), (274, -480)]

def row2362 : Integer.Sparse (Fin 3237) := [(0, -2), (1, -10), (3, -550), (4, 65), (11, -480), (32, 360), (34, 120), (35, 80), (37, 160), (47, 360), (66, 440), (67, -360), (68, 1200), (71, 480), (91, 720), (116, 1440), (120, 720), (139, 720), (159, -960), (160, 2960), (162, 1680), (165, 1360), (219, -480), (225, 720), (232, 720), (249, -120), (251, -480), (253, -240), (254, 80), (255, 480), (256, 520), (261, -195), (271, 720)]

def row2363 : Integer.Sparse (Fin 3237) := [(0, -8), (3, -1000), (4, 130), (32, 605), (55, 720), (66, 480), (68, 2160), (71, 640), (116, 2880), (120, 2880), (135, 1440), (139, 1440), (159, -1200), (160, 5600), (162, 2880), (165, 2480), (194, 1440), (219, -960), (224, -240), (225, 1280), (230, 1440), (232, 1440), (251, -960), (253, -960), (254, 240), (255, 1440), (256, 1280), (261, -345), (271, 1440)]

def row2364 : Integer.Sparse (Fin 3237) := [(0, -29), (1, -20), (3, -1460), (4, 210), (8, -960), (24, -960), (32, 835), (34, 240), (35, 160), (42, 720), (45, 1440), (62, -720), (64, -720), (66, 1200), (68, 2560), (69, 800), (71, 640), (76, 2880), (99, 1440), (160, 4080), (162, 3840), (163, 800), (165, 3040), (166, 720), (172, 1440), (185, 1440), (214, -960), (216, -240), (219, -960), (220, -720), (225, 1280), (227, -1920), (242, 1440), (261, 370)]

def row2365 : Integer.Sparse (Fin 3237) := [(0, -1), (3, -40), (20, -960), (24, -1440), (31, 60), (32, 105), (52, 2160), (57, 2160), (62, -720), (66, 480), (68, 320), (153, -720), (156, -720), (160, 2400), (162, 640), (215, -480), (217, -1440), (218, -2160), (222, -2160), (224, -2880), (225, 1200), (226, -720), (252, -1440), (256, 720), (260, 300), (261, -370)]

def row2366 : Integer.Sparse (Fin 3237) := [(0, -2), (1, -4), (3, -36), (4, 3), (7, -288), (20, -96), (24, -288), (31, 24), (32, 24), (34, 48), (35, 32), (41, 432), (54, 432), (65, -144), (66, 192), (68, 96), (153, -288), (159, -432), (160, 432), (162, 64), (214, -144), (215, -192), (216, -144), (218, -432), (219, -576), (225, 240), (252, -144), (256, 48), (260, 84), (261, -69)]

def row2367 : Integer.Sparse (Fin 3237) := [(1, -8), (3, -216), (4, 16), (11, -96), (31, 24), (32, 175), (34, 96), (35, 48), (37, 80), (65, -48), (66, 416), (67, -48), (68, 176), (71, 336), (85, 144), (91, 144), (108, 288), (125, 144), (127, 288), (142, 144), (156, -288), (159, -528), (160, 784), (162, 32), (165, 144), (217, -96), (222, -336), (224, -96), (225, 32), (228, 288), (229, 144), (231, 144), (251, -96), (255, 112), (256, 192), (260, 96), (261, -93), (266, -96), (267, -48), (268, -96), (273, -96), (274, -192)]

def row2368 : Integer.Sparse (Fin 3237) := [(0, -7), (3, -460), (4, 25), (8, -1440), (10, 320), (24, -1440), (32, 570), (61, -1440), (64, -720), (66, 1440), (68, 2080), (69, 240), (71, 480), (72, 2160), (75, 2160), (79, 4320), (84, 4320), (86, 1440), (93, 4320), (94, 4320), (99, 2160), (101, 4320), (152, -720), (155, -960), (159, -720), (160, 6160), (162, 2880), (163, 480), (165, 1520), (219, -2160), (224, -720), (225, 2000), (252, -1440), (253, -2160), (255, 1440), (256, 1440), (261, -580), (274, -720)]

def row2369 : Integer.Sparse (Fin 3237) := [(0, 21), (3, -580), (4, 30), (32, 350), (61, -1440), (64, -720), (66, 1920), (68, 2000), (69, 240), (71, 960), (74, 2160), (79, 4320), (98, 2160), (102, 4320), (160, 6240), (162, 640), (165, 240), (169, 4320), (175, 4320), (224, -720), (225, 480), (247, 1440), (248, 4320), (249, -960), (251, -2160), (253, -3120), (254, 240), (255, 3120), (256, 2720), (261, -705)]

def row2370 : Integer.Sparse (Fin 3237) := [(1, -4), (3, -64), (4, 9), (7, -288), (24, -576), (31, 12), (32, 19), (34, 48), (35, 32), (41, 432), (62, -288), (65, -144), (66, 144), (68, 224), (73, 432), (78, 864), (96, 432), (97, 432), (101, 864), (150, -288), (153, -144), (159, -288), (160, 432), (165, 144), (166, 864), (174, 864), (214, -432), (215, -96), (216, -336), (218, -144), (219, -720), (224, -144), (225, 144), (226, -48), (243, 864), (246, 288), (250, -144), (252, -288), (253, -144), (254, 48), (255, 96), (256, 96), (260, 36), (261, -78), (267, -144), (274, -288)]

def row2371 : Integer.Sparse (Fin 3237) := [(0, 1), (3, -160), (4, 14), (27, 128), (32, 113), (61, -672), (66, 560), (68, 896), (71, 128), (74, 144), (75, 432), (79, 576), (137, 288), (160, 1488), (165, 368), (205, 288), (208, 576), (209, 288), (253, -816), (254, 128), (255, 896), (256, 512), (261, -98)]

def row2372 : Integer.Sparse (Fin 3237) := [(0, -9), (1, -40), (3, -1400), (4, 190), (7, -480), (24, -960), (31, 60), (32, 600), (34, 640), (35, 480), (61, -960), (62, -960), (65, -480), (66, 2400), (68, 3520), (71, 480), (73, 720), (74, 720), (78, 1440), (79, 1440), (85, 1440), (98, 1440), (112, 1440), (150, -480), (153, -240), (156, -480), (159, -480), (160, 4480), (165, 2560), (176, 2880), (186, 1440), (214, -720), (217, -480), (222, -480), (224, -480), (226, -240), (247, 1440), (253, -3360), (254, 640), (255, 1920), (256, 1120), (260, 120), (261, -25), (267, -480), (274, -480)]

def row2373 : Integer.Sparse (Fin 3237) := [(0, -2), (3, -152), (4, 8), (8, -288), (24, -192), (27, 64), (32, 107), (43, 288), (44, 288), (45, 288), (61, -288), (63, -144), (64, -288), (66, 480), (68, 544), (71, 224), (75, 144), (79, 288), (84, 288), (94, 576), (98, 288), (101, 288), (102, 288), (123, 144), (126, 288), (160, 1024), (162, 176), (165, 160), (169, 576), (171, 288), (174, 288), (175, 864), (219, -48), (223, -192), (224, -288), (225, 208), (227, -48), (251, -96), (252, -48), (253, -288), (254, 48), (255, 384), (256, 288), (261, -63)]

def row2374 : Integer.Sparse (Fin 3237) := [(0, -11), (3, -980), (4, 145), (24, -960), (32, 415), (61, -960), (62, -1440), (66, 640), (68, 2320), (69, 320), (71, 480), (73, 1440), (74, 720), (79, 1440), (93, 2880), (98, 1440), (101, 1440), (102, 1440), (160, 4080), (162, 2320), (163, 320), (165, 2080), (168, 1440), (176, 1440), (186, 2880), (214, -480), (219, -720), (220, -240), (224, -1440), (225, 880), (226, -960), (227, -480), (242, 1440), (243, 1440), (247, 1440), (248, 4320), (251, -480), (253, -1920), (254, 320), (255, 1280), (256, 880), (261, -15)]

def row2375 : Integer.Sparse (Fin 3237) := [(0, 7), (1, -4), (3, -128), (4, 7), (31, 48), (32, 152), (34, 32), (35, 16), (37, 32), (65, -48), (66, 192), (68, 48), (71, 224), (125, 576), (145, 144), (154, -192), (156, -480), (159, -144), (160, 544), (165, 64), (183, 288), (200, 144), (217, -96), (218, -336), (222, -960), (224, -528), (225, 48), (255, 32), (256, 256), (260, 324), (261, -142), (262, 288), (266, -192), (267, -192), (273, -384), (274, -288)]

def row2376 : Integer.Sparse (Fin 3237) := [(0, -18), (1, -60), (3, -1260), (4, 135), (8, -720), (9, -480), (10, 560), (31, 60), (32, 700), (34, 800), (35, 400), (48, 720), (61, -960), (62, -480), (65, -240), (66, 2240), (68, 3200), (69, 80), (71, 720), (75, 1440), (86, 1440), (99, 720), (110, 720), (111, 720), (154, -720), (155, -240), (156, -480), (160, 3040), (162, 1440), (163, 400), (165, 2960), (167, 1440), (185, 720), (186, 1440), (218, -240), (219, -240), (224, -240), (225, 320), (226, -240), (227, -240), (253, -480), (255, 160), (256, 160), (260, 60), (261, 295), (267, -240)]

def row2377 : Integer.Sparse (Fin 3237) := [(0, -24), (3, -1360), (4, 175), (8, -1920), (10, 640), (24, -480), (32, 715), (43, 720), (44, 720), (45, 720), (61, -480), (62, -720), (64, -720), (66, 1760), (68, 3920), (69, 960), (71, 800), (75, 720), (76, 1440), (87, 1440), (106, 720), (111, 720), (118, 720), (160, 4240), (162, 4400), (163, 1360), (165, 3440), (168, 720), (170, 1440), (176, 720), (190, 720), (214, -480), (219, -720), (220, -960), (225, 1280), (227, -1680), (242, 720), (253, -480), (254, 80), (255, 160), (256, 80), (261, 360)]

def row2378 : Integer.Sparse (Fin 3237) := [(0, -31), (3, -400), (4, 15), (8, -3360), (10, 640), (24, -960), (25, -480), (29, 320), (32, 410), (42, 720), (43, 720), (44, 1440), (45, 1440), (64, -2640), (66, 2320), (68, 3680), (69, 640), (71, 320), (72, 2880), (75, 1440), (76, 2880), (82, 1440), (99, 1440), (159, -960), (160, 6720), (162, 5760), (163, 640), (165, 1760), (218, -240), (219, -960), (220, -720), (224, -480), (225, 3120), (227, -720), (253, -480), (255, 320), (256, 160), (260, 60), (261, -330)]

def row2379 : Integer.Sparse (Fin 3237) := [(0, -6), (3, -220), (4, 20), (8, -480), (24, -1440), (25, -240), (29, 160), (32, 175), (42, 360), (44, 720), (61, -960), (64, -120), (66, 400), (68, 560), (71, 240), (72, 720), (73, 1440), (74, 720), (77, 1440), (79, 1440), (80, 720), (84, 720), (93, 1440), (94, 2880), (97, 720), (101, 1440), (152, -720), (155, -480), (159, -480), (160, 2560), (162, 720), (165, 240), (218, -120), (219, -1200), (220, -360), (224, -960), (225, 760), (252, -240), (253, -960), (255, 800), (256, 720), (260, 30), (261, -205), (274, -240)]

def row2380 : Integer.Sparse (Fin 3237) := [(0, 9), (3, -400), (4, 45), (27, 160), (32, 380), (43, 720), (45, 1440), (61, -1440), (66, 1360), (68, 3040), (71, 160), (75, 1440), (79, 2880), (98, 1440), (102, 2880), (160, 6240), (162, 640), (165, 1280), (169, 1440), (171, 1440), (175, 5760), (186, 2880), (224, -1440), (225, 480), (227, -720), (248, 2880), (249, -960), (251, -1440), (253, -2880), (254, 480), (255, 3040), (256, 2400), (261, -570)]

def row2381 : Integer.Sparse (Fin 3237) := [(0, -12), (3, -900), (4, 130), (8, -960), (24, -960), (32, 375), (42, 720), (44, 1440), (62, -480), (64, -240), (66, 880), (68, 2480), (69, 320), (71, 480), (76, 1440), (78, 2880), (96, 1440), (99, 1440), (100, 2880), (101, 2880), (150, -1920), (159, -1440), (160, 3920), (162, 1680), (163, 320), (165, 1920), (166, 1440), (172, 1440), (174, 5760), (185, 2880), (214, -1440), (216, -960), (218, -240), (219, -3120), (220, -960), (225, 1120), (227, -480), (243, 2880), (250, -1440), (251, -480), (252, -1920), (253, -1440), (254, 480), (255, 1280), (256, 800), (260, 60), (261, -195), (267, -480), (274, -960)]

def row2382 : Integer.Sparse (Fin 3237) := [(0, -13), (3, -700), (4, 30), (8, -480), (21, -960), (22, -480), (27, 800), (32, 375), (42, 720), (43, 1440), (61, -1920), (64, -240), (66, 2960), (68, 3680), (71, 960), (75, 1440), (82, 1440), (99, 720), (121, 1440), (123, 1440), (159, -480), (160, 3840), (162, 80), (165, 1120), (167, 1440), (218, -240), (219, -720), (220, -240), (222, -480), (224, -480), (225, 160), (252, -480), (253, -480), (255, 1760), (256, 800), (260, 60), (261, -150)]

def row2383 : Integer.Sparse (Fin 3237) := [(0, -9), (3, -860), (4, 70), (24, -480), (27, 640), (28, -480), (29, 320), (32, 565), (43, 720), (61, -2880), (66, 3120), (68, 4800), (71, 800), (74, 720), (75, 1440), (79, 2880), (81, 1440), (98, 720), (126, 1440), (137, 1440), (160, 7040), (162, 160), (165, 1920), (176, 1440), (208, 1440), (225, 80), (227, -240), (251, -240), (253, -4320), (254, 640), (255, 3920), (256, 2160), (261, -280)]

def row2384 : Integer.Sparse (Fin 3237) := [(0, -12), (3, -1320), (4, 175), (8, -960), (10, 160), (24, -480), (32, 615), (43, 720), (61, -480), (62, -480), (64, -240), (66, 1760), (68, 3840), (69, 80), (71, 720), (75, 720), (76, 720), (78, 1440), (79, 1440), (87, 1440), (106, 720), (112, 1440), (120, 1440), (150, -960), (159, -960), (160, 4880), (162, 1040), (163, 240), (165, 3200), (170, 720), (176, 1440), (190, 1440), (214, -720), (222, -240), (225, 320), (227, -240), (251, -480), (253, -3120), (254, 640), (255, 1840), (256, 1120), (260, 60), (261, -20), (267, -480), (274, -480)]

def row2385 : Integer.Sparse (Fin 3237) := [(0, -2), (3, -116), (4, 6), (8, -192), (22, -96), (24, -288), (29, 64), (32, 93), (42, 144), (45, 288), (61, -384), (63, -288), (64, -144), (66, 272), (68, 256), (71, 192), (74, 288), (79, 576), (80, 288), (94, 576), (97, 144), (102, 288), (124, 288), (126, 576), (160, 976), (162, 192), (165, 64), (166, 288), (169, 576), (175, 1152), (219, -144), (220, -48), (223, -192), (224, -144), (225, 112), (251, -192), (253, -384), (255, 416), (256, 352), (261, -39)]

def row2386 : Integer.Sparse (Fin 3237) := [(0, -13), (3, -1220), (4, 170), (8, -480), (10, 160), (32, 605), (61, -960), (62, -720), (66, 1200), (68, 3040), (69, 560), (71, 640), (75, 1440), (79, 2880), (86, 1440), (93, 2880), (99, 720), (102, 1440), (160, 4480), (162, 2880), (163, 560), (165, 2720), (167, 720), (185, 1440), (186, 2880), (219, -480), (220, -480), (224, -720), (225, 720), (226, -960), (227, -960), (242, 1440), (248, 5760), (251, -960), (253, -1440), (255, 960), (256, 800), (261, 80)]

def row2387 : Integer.Sparse (Fin 3237) := [(0, -5), (3, -216), (4, 24), (8, -240), (10, 160), (16, -192), (18, -96), (32, 127), (42, 144), (43, 288), (46, 288), (61, -192), (62, -96), (64, -48), (66, 384), (68, 720), (69, 32), (71, 128), (110, 288), (111, 288), (159, -96), (160, 656), (162, 512), (163, 112), (165, 544), (167, 288), (170, 288), (218, -48), (219, -192), (220, -96), (225, 112), (227, -96), (260, 12), (261, 76), (267, -96)]

def row2388 : Integer.Sparse (Fin 3237) := [(0, -29), (3, -1500), (4, 190), (8, -1920), (10, 640), (17, 320), (18, -480), (32, 855), (42, 720), (43, 1440), (45, 1440), (46, 1440), (61, -960), (62, -720), (64, -720), (66, 1680), (68, 3680), (69, 880), (71, 960), (118, 2880), (160, 4480), (162, 5120), (163, 1680), (165, 4160), (167, 720), (170, 2880), (220, -720), (225, 1120), (227, -2400), (242, 1440), (261, 550)]

def row2389 : Integer.Sparse (Fin 3237) := [(0, -38), (1, -20), (3, -820), (4, 30), (7, -1440), (8, -3600), (31, 60), (32, 555), (34, 240), (35, 160), (41, 2160), (42, 4320), (44, 4320), (64, -2160), (65, -720), (66, 2880), (68, 1760), (69, 240), (71, 1440), (84, 2160), (99, 2160), (153, -720), (159, -4320), (160, 5040), (162, 4000), (172, 1440), (215, -480), (216, -720), (218, -1440), (219, -4320), (220, -2400), (223, -240), (224, -720), (225, 2720), (260, 360), (261, -325)]

def row2390 : Integer.Sparse (Fin 3237) := [(0, -14), (3, -660), (4, 45), (8, -480), (10, 320), (25, -480), (27, 160), (29, 160), (32, 255), (43, 720), (61, -480), (64, -240), (66, 3040), (68, 3840), (71, 640), (72, 1440), (74, 1440), (75, 3600), (81, 1440), (98, 1440), (159, -480), (160, 3440), (162, 960), (165, 1520), (222, -240), (224, -480), (225, 640), (253, -1200), (255, 960), (256, 400), (260, 60), (261, -100)]

def row2391 : Integer.Sparse (Fin 3237) := [(0, -3), (1, -8), (3, -164), (4, 9), (7, -96), (8, -240), (27, 32), (31, 12), (32, 91), (34, 128), (35, 96), (43, 576), (61, -96), (64, -192), (65, -96), (66, 592), (68, 512), (71, 256), (75, 144), (84, 144), (85, 288), (98, 288), (153, -48), (156, -96), (159, -288), (160, 656), (162, 64), (165, 144), (169, 288), (171, 288), (217, -96), (222, -192), (223, -48), (224, -96), (225, 80), (253, -48), (255, 96), (256, 48), (260, 48), (261, -31)]

def row2392 : Integer.Sparse (Fin 3237) := [(0, -12), (3, -1040), (4, 70), (8, -480), (24, -960), (25, -480), (27, 160), (29, 160), (32, 775), (43, 720), (61, -3840), (64, -240), (66, 2800), (68, 3280), (71, 1280), (72, 720), (74, 2880), (75, 2880), (77, 1440), (79, 4320), (81, 1440), (98, 1440), (152, -720), (159, -480), (160, 6320), (162, 80), (165, 1760), (222, -240), (224, -480), (225, 80), (253, -4080), (254, 240), (255, 2880), (256, 1840), (260, 60), (261, -195), (274, -240)]

def row2393 : Integer.Sparse (Fin 3237) := [(0, -1), (3, -1120), (4, 105), (27, 160), (32, 730), (61, -2880), (66, 3040), (68, 4160), (71, 960), (74, 1440), (75, 3600), (79, 4320), (160, 6400), (165, 2240), (205, 1440), (208, 1440), (209, 1440), (253, -4800), (254, 560), (255, 3520), (256, 2080), (261, -310)]

def row2394 : Integer.Sparse (Fin 3237) := [(0, -14), (1, -60), (3, -440), (4, 70), (9, -480), (21, -480), (22, -480), (27, 400), (31, 60), (32, 45), (34, 800), (35, 400), (42, 1440), (48, 720), (64, -480), (65, -240), (66, 1680), (68, 2480), (71, 640), (74, 1440), (80, 1440), (97, 720), (123, 720), (154, -720), (155, -240), (156, -480), (160, 2320), (165, 480), (166, 720), (169, 1440), (218, -480), (219, -1200), (220, -480), (223, -240), (224, -240), (252, -240), (253, -960), (255, 640), (260, 120), (261, -15)]

def row2395 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -196), (4, 20), (8, -48), (10, 32), (27, 64), (28, -96), (29, 32), (32, 108), (43, 288), (61, -384), (66, 480), (68, 768), (71, 176), (74, 144), (75, 432), (81, 288), (98, 144), (126, 144), (137, 144), (160, 768), (162, 112), (163, 16), (165, 480), (176, 144), (208, 144), (225, 32), (227, -96), (251, -48), (253, -288), (254, 16), (255, 272), (256, 144), (261, 15)]

def row2396 : Integer.Sparse (Fin 3237) := [(0, -33), (3, -1600), (4, 100), (8, -3840), (10, 160), (22, -480), (24, -480), (29, 160), (32, 950), (42, 1440), (43, 2880), (44, 1440), (45, 2880), (61, -1440), (63, -720), (64, -2400), (66, 3680), (68, 3440), (69, 320), (71, 2240), (75, 1440), (82, 1440), (99, 720), (124, 720), (126, 1440), (160, 4480), (162, 2560), (163, 400), (165, 2240), (167, 720), (219, -240), (220, -720), (225, 1360), (227, -960), (253, -480), (255, 160), (256, 160), (261, 235)]

def row2397 : Integer.Sparse (Fin 3237) := [(0, -29), (3, -1080), (4, 60), (8, -2880), (10, 480), (24, -1440), (32, 1290), (61, -1440), (64, -720), (66, 1680), (68, 1680), (69, 240), (71, 1440), (72, 2160), (89, 4320), (90, 4320), (92, 4320), (115, 4320), (152, -720), (159, -2880), (160, 6720), (162, 4400), (163, 960), (165, 3120), (225, 2160), (256, 960), (261, -45), (274, -720)]

def row2398 : Integer.Sparse (Fin 3237) := [(0, 3), (3, -1720), (4, 150), (27, 800), (32, 1095), (61, -3360), (66, 3040), (68, 4000), (71, 1760), (89, 2880), (137, 1440), (160, 6480), (165, 2640), (253, -720), (254, 240), (255, 2560), (256, 1520), (261, -230), (269, 4320), (272, 1440)]

def row2399 : Integer.Sparse (Fin 3237) := [(0, -16), (3, -1820), (4, 95), (8, -960), (24, -960), (27, 480), (32, 1155), (51, 1440), (61, -2400), (63, -720), (66, 3760), (68, 2480), (71, 3040), (89, 1440), (90, 2880), (109, 720), (115, 1440), (123, 720), (126, 1440), (127, 1440), (159, -960), (160, 4000), (162, 160), (165, 1120), (173, 1440), (225, 80), (227, -240), (251, -240), (255, 1120), (256, 880), (261, 140), (268, -720), (274, -960)]

def row2400 : Integer.Sparse (Fin 3237) := [(0, -1), (1, -4), (3, -412), (4, 60), (24, -192), (32, 143), (34, 16), (37, 64), (62, -144), (66, 48), (68, 288), (71, 256), (78, 576), (96, 144), (101, 288), (150, -192), (160, 304), (165, 608), (166, 144), (174, 288), (214, -192), (216, -48), (219, -96), (225, 16), (242, 288), (243, 288), (250, -48), (252, -96), (253, -96), (254, 32), (255, 64), (256, 32), (261, 64), (267, -144), (270, 288), (274, -192)]

def row2401 : Integer.Sparse (Fin 3237) := [(0, -27), (1, -20), (3, -2140), (4, 250), (8, -1200), (9, -480), (10, 720), (11, -480), (32, 1080), (34, 160), (37, 560), (50, 720), (66, 2160), (67, -720), (68, 3680), (69, 400), (71, 1920), (89, 1440), (91, 1440), (92, 1440), (111, 720), (155, -240), (159, -480), (160, 3840), (162, 2640), (163, 800), (165, 4080), (219, -240), (220, -240), (225, 560), (227, -960), (261, 505)]

def row2402 : Integer.Sparse (Fin 3237) := [(0, -29), (3, -2000), (4, 240), (8, -1920), (10, 800), (32, 1010), (51, 720), (66, 1600), (68, 3120), (69, 240), (71, 1600), (89, 720), (92, 1440), (111, 720), (115, 720), (116, 720), (118, 720), (120, 720), (159, -480), (160, 3600), (162, 2720), (163, 880), (165, 4240), (173, 1440), (225, 560), (227, -960), (251, -480), (255, 80), (256, 160), (257, 720), (261, 535)]

def row2403 : Integer.Sparse (Fin 3237) := [(0, -21), (1, -20), (3, -1240), (4, 200), (8, -480), (32, 450), (34, 80), (37, 320), (44, 720), (66, 640), (68, 1360), (69, 160), (71, 1040), (78, 1440), (100, 720), (101, 720), (150, -480), (159, -480), (160, 1440), (162, 720), (163, 400), (165, 2000), (174, 2160), (185, 720), (214, -480), (216, -240), (219, -480), (220, -240), (225, 160), (227, -480), (243, 720), (250, -240), (251, -480), (252, -240), (253, -480), (254, 160), (255, 320), (256, 160), (261, 275)]

def row2404 : Integer.Sparse (Fin 3237) := [(0, -23), (3, -1300), (4, 90), (8, -2400), (10, 320), (24, -1920), (25, -480), (29, 320), (32, 1130), (44, 720), (51, 1440), (61, -960), (64, -240), (66, 1760), (68, 1040), (71, 2000), (72, 2160), (77, 1440), (78, 2880), (79, 1440), (83, 1440), (89, 1440), (90, 2880), (92, 1440), (101, 1440), (115, 1440), (152, -720), (159, -3120), (160, 5680), (162, 2800), (163, 480), (165, 1920), (222, -240), (224, -480), (225, 1600), (227, -720), (251, -960), (253, -480), (255, 480), (256, 1200), (260, 60), (261, -105), (274, -720)]

def row2405 : Integer.Sparse (Fin 3237) := [(0, -14), (1, -20), (3, -1260), (4, 175), (7, -480), (11, -960), (24, -960), (31, 60), (32, 500), (34, 80), (37, 320), (47, 720), (49, 1440), (62, -960), (65, -480), (66, 480), (67, -240), (68, 2080), (69, 640), (71, 960), (73, 720), (78, 1440), (92, 1440), (93, 1440), (101, 1440), (112, 1440), (115, 1440), (150, -480), (153, -240), (156, -480), (159, -960), (160, 3840), (162, 2880), (163, 640), (165, 2080), (168, 2880), (173, 1440), (214, -720), (217, -480), (219, -960), (220, -480), (222, -480), (224, -480), (225, 960), (226, -240), (227, -960), (243, 1440), (249, -720), (251, -2400), (255, 800), (256, 960), (257, 2880), (260, 120), (261, 15), (267, -480), (274, -480)]

def row2406 : Integer.Sparse (Fin 3237) := [(0, -2), (3, -170), (4, 8), (8, -48), (21, -48), (22, -48), (24, -72), (27, 40), (29, 16), (32, 115), (44, 72), (61, -240), (63, -72), (66, 384), (68, 232), (71, 296), (79, 144), (83, 144), (89, 144), (90, 144), (101, 72), (113, 72), (123, 72), (124, 72), (126, 144), (127, 144), (159, -48), (160, 424), (162, 40), (165, 80), (168, 144), (219, -48), (220, -24), (225, 32), (252, -24), (253, -48), (255, 104), (256, 64), (261, 11), (268, -72), (274, -48)]

def row2407 : Integer.Sparse (Fin 3237) := [(0, -6), (3, -340), (4, 31), (8, -48), (24, -96), (27, 32), (32, 193), (45, 144), (61, -288), (66, 448), (68, 384), (71, 384), (79, 432), (89, 288), (126, 288), (160, 624), (162, 64), (163, 16), (165, 368), (176, 144), (225, 16), (227, -48), (242, 144), (253, -288), (254, 32), (255, 176), (256, 80), (261, 72), (269, 144)]

def row2408 : Integer.Sparse (Fin 3237) := [(0, 27), (1, -20), (3, -400), (4, 20), (11, -480), (31, 180), (32, 610), (34, 80), (37, 80), (65, -240), (66, 240), (67, -240), (71, 560), (145, 720), (153, -240), (156, -1440), (159, -5040), (160, 2960), (165, 400), (183, 720), (218, -240), (222, -1680), (225, 560), (236, 720), (237, 1440), (238, 720), (239, 1440), (241, 1440), (251, -960), (255, 160), (256, 2000), (260, 900), (261, -905), (268, -960), (274, -2400)]

def row2409 : Integer.Sparse (Fin 3237) := [(0, 33), (3, -380), (4, 45), (24, -480), (27, 640), (29, 640), (32, 305), (61, -960), (66, 1120), (68, 2000), (71, 80), (108, 720), (112, 1440), (134, 1440), (137, 1440), (138, 1440), (140, 1440), (160, 6480), (162, 400), (165, 1040), (222, -240), (225, 400), (255, 3360), (256, 2720), (261, -685), (274, -720)]

def row2410 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -68), (4, 5), (8, -192), (21, -144), (24, -672), (27, 64), (29, 64), (32, 91), (61, -192), (63, -144), (66, 144), (68, 224), (71, 64), (108, 144), (120, 288), (121, 288), (123, 144), (126, 288), (129, 144), (130, 288), (135, 288), (144, 288), (159, -48), (160, 768), (162, 176), (165, 160), (225, 176), (227, -48), (252, -192), (255, 256), (256, 192), (261, -39), (274, -144)]

def row2411 : Integer.Sparse (Fin 3237) := [(0, -11), (1, -20), (3, -520), (4, 35), (9, -480), (21, -2880), (24, -3840), (31, 180), (32, 850), (34, 80), (35, 80), (66, 640), (67, -480), (68, 400), (71, 320), (105, 1440), (153, -240), (154, -960), (156, -480), (159, -5760), (160, 5920), (162, 1440), (165, 800), (181, 720), (183, 1440), (188, 2880), (192, 1440), (218, -1200), (219, -960), (224, -2160), (225, 2000), (252, -2880), (255, 480), (256, 1280), (260, 720), (261, -790), (268, -1920), (274, -3840)]

def row2412 : Integer.Sparse (Fin 3237) := [(0, -21), (1, -60), (3, -900), (4, 170), (20, -2640), (24, -1920), (31, 180), (32, 365), (34, 240), (35, 160), (62, -720), (66, 560), (68, 1760), (150, -960), (153, -240), (154, -480), (156, -480), (160, 4080), (162, 4160), (165, 2240), (166, 720), (177, 720), (191, 1440), (214, -960), (215, -720), (216, -240), (218, -960), (219, -1440), (225, 1200), (242, 1440), (252, -960), (260, 240), (261, 80), (264, 1440), (267, -1920), (274, -960)]

def row2413 : Integer.Sparse (Fin 3237) := [(0, -26), (1, -20), (3, -320), (4, 5), (7, -480), (8, -1200), (31, 120), (32, 380), (34, 160), (64, -960), (65, -480), (66, 1040), (68, 160), (71, 480), (84, 720), (99, 720), (145, 1440), (153, -720), (154, -480), (156, -240), (159, -3120), (160, 3600), (162, 1920), (165, 80), (181, 1440), (183, 1440), (184, 1440), (218, -1200), (219, -480), (222, -480), (223, -240), (224, -1680), (225, 1920), (238, 720), (256, 160), (260, 660), (261, -335)]

def row2414 : Integer.Sparse (Fin 3237) := [(0, -9), (1, -20), (3, -320), (4, 40), (9, -480), (21, -960), (24, -480), (32, -35), (34, 240), (66, 2240), (68, 960), (71, 320), (84, 720), (99, 720), (105, 1440), (109, 2880), (153, -480), (155, -240), (159, -480), (160, 3040), (162, 80), (165, 160), (218, -480), (219, -2640), (225, 320), (252, -2160), (253, -960), (255, 1440), (256, 800), (261, -10)]

def row2415 : Integer.Sparse (Fin 3237) := [(0, 6), (1, -20), (3, -480), (4, 35), (11, -480), (32, 565), (34, 160), (37, 80), (61, -1200), (66, 800), (68, 320), (71, 880), (98, 720), (127, 1440), (142, 1440), (153, -240), (156, -240), (159, -1440), (160, 4160), (165, 800), (169, 720), (222, -240), (228, 1440), (234, 1440), (237, 1440), (249, -240), (251, -1680), (253, -960), (255, 1520), (256, 1680), (260, 60), (261, -240), (274, -480)]

def row2416 : Integer.Sparse (Fin 3237) := [(0, 1), (1, -40), (3, -740), (4, 65), (31, 120), (32, 640), (34, 160), (37, 240), (64, -480), (65, -240), (66, 880), (68, 560), (71, 1120), (102, 720), (108, 1440), (135, 720), (154, -480), (156, -960), (159, -2160), (160, 3520), (162, 720), (165, 800), (175, 720), (183, 720), (193, 1440), (194, 720), (218, -480), (222, -240), (223, -240), (224, -1200), (225, 800), (231, 720), (240, 720), (254, 80), (255, 480), (256, 720), (260, 420), (261, -490), (266, -480), (267, -240), (268, -240), (273, -240), (274, -720)]

def row2417 : Integer.Sparse (Fin 3237) := [(0, -14), (1, -20), (3, -760), (4, 115), (9, -480), (10, 560), (21, -480), (29, 560), (32, 360), (34, 160), (37, 80), (66, 1120), (68, 2320), (69, 80), (71, 240), (93, 720), (101, 720), (111, 720), (112, 1440), (119, 1440), (120, 1440), (136, 720), (155, -240), (156, -480), (160, 4400), (162, 2640), (163, 400), (165, 2480), (219, -1440), (225, 560), (252, -240), (253, -480), (255, 1360), (256, 640), (261, -145)]

def row2418 : Integer.Sparse (Fin 3237) := [(0, 3), (3, -60), (4, 6), (32, 51), (61, -48), (66, 80), (68, 144), (71, 72), (127, 216), (135, 72), (139, 72), (159, -120), (160, 608), (162, 64), (165, 64), (194, 72), (225, 64), (234, 144), (235, 144), (251, -96), (253, -48), (254, 24), (255, 240), (256, 232), (260, 6), (261, -80), (267, -24), (268, -72), (269, 72), (271, 72), (272, 72), (274, -72)]

def row2419 : Integer.Sparse (Fin 3237) := [(0, -29), (3, -800), (4, 110), (8, -960), (10, 640), (24, -480), (29, 640), (32, 660), (66, 480), (68, 2320), (69, 240), (71, 240), (92, 720), (110, 1440), (111, 720), (112, 720), (115, 720), (116, 1440), (117, 1440), (118, 720), (120, 720), (136, 720), (141, 720), (159, -240), (160, 5920), (162, 5520), (163, 800), (165, 3120), (225, 1840), (227, -480), (255, 880), (256, 560), (261, -5), (267, -240)]

def row2420 : Integer.Sparse (Fin 3237) := [(0, -36), (1, -20), (3, -860), (4, 100), (7, -480), (8, -1440), (24, -960), (32, 615), (34, 80), (37, 160), (66, 560), (68, 640), (69, 160), (71, 800), (99, 720), (116, 1440), (156, -480), (159, -1440), (160, 3440), (162, 3360), (163, 400), (165, 1840), (184, 1440), (185, 720), (214, -480), (216, -240), (219, -1200), (220, -480), (225, 1200), (232, 1440), (261, 35), (267, -480)]

def row2421 : Integer.Sparse (Fin 3237) := [(0, -18), (3, -260), (4, 45), (10, 720), (29, 2400), (32, 160), (68, 1920), (69, 80), (87, 720), (106, 720), (117, 1440), (160, 7200), (162, 3680), (163, 160), (165, 880), (180, 1440), (206, 1440), (224, -480), (225, 1280), (235, 1440), (251, -720), (254, 80), (255, 3120), (256, 1520), (261, -455), (268, -480)]

def row2422 : Integer.Sparse (Fin 3237) := [(0, -38), (1, -20), (3, -560), (4, 75), (9, -480), (10, 560), (21, -1440), (29, 1920), (31, 120), (32, 240), (35, 80), (37, 80), (66, 640), (67, -480), (68, 2320), (69, 320), (71, 160), (86, 720), (99, 720), (119, 1440), (154, -480), (159, -1440), (160, 5840), (162, 4160), (163, 400), (165, 1280), (179, 1440), (180, 1440), (193, 720), (217, -720), (218, -240), (219, -480), (224, -1200), (225, 1360), (226, -240), (255, 2240), (256, 160), (258, 1440), (260, 180), (261, -205), (266, -240), (268, -960)]

def row2423 : Integer.Sparse (Fin 3237) := [(0, -3), (3, -210), (4, 30), (21, -720), (27, 360), (29, 960), (32, 45), (66, 280), (68, 1240), (71, 120), (127, 360), (134, 720), (159, -120), (160, 3440), (162, 800), (165, 200), (180, 720), (194, 360), (205, 360), (206, 720), (209, 360), (224, -360), (225, 80), (251, -480), (253, -120), (254, 160), (255, 2200), (256, 1000), (261, -280), (268, -480), (271, 360)]

def row2424 : Integer.Sparse (Fin 3237) := [(0, -22), (1, -40), (3, -620), (4, 95), (21, -2400), (24, -480), (27, 560), (29, 1520), (31, 120), (32, 355), (34, 160), (35, 240), (63, -480), (66, 1280), (67, -240), (68, 2400), (71, 240), (98, 720), (144, 1440), (154, -1200), (156, -240), (159, -1440), (160, 5680), (162, 2400), (165, 1120), (171, 720), (179, 1440), (180, 1440), (187, 720), (193, 720), (194, 720), (217, -480), (222, -240), (223, -240), (224, -960), (225, 480), (229, 720), (235, 720), (254, 80), (255, 3040), (256, 800), (260, 120), (261, -190), (267, -240), (268, -1200), (274, -240)]

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

def row256 : Integer.Sparse (Fin 3237) := [(2147, 1), (2746, 1), (2747, 1), (2749, 1), (2768, 1), (2783, 1), (2839, -1)]

def row257 : Integer.Sparse (Fin 3237) := [(903, 1), (906, 1), (908, 1), (914, 1), (943, 1), (2147, 1), (2839, -1)]

def row258 : Integer.Sparse (Fin 3237) := [(914, 1), (2050, 1), (2109, 1), (2147, 2), (2159, 1), (2839, -1)]

def row259 : Integer.Sparse (Fin 3237) := [(1863, 1), (2091, 1), (2121, 1), (2123, 1), (2147, 1), (2747, 1), (2839, -1)]

def row260 : Integer.Sparse (Fin 3237) := [(903, 1), (2030, 1), (2121, 1), (2137, 1), (2145, 1), (2147, 1), (2839, -1)]

def row261 : Integer.Sparse (Fin 3237) := [(1862, 1), (2075, 1), (2105, 1), (2109, 1), (2147, 1), (2746, 1), (2839, -1)]

def row262 : Integer.Sparse (Fin 3237) := [(943, 1), (1862, 1), (1863, 1), (1873, 1), (1959, 1), (2147, 1), (2839, -1)]

def row263 : Integer.Sparse (Fin 3237) := [(2030, 1), (2032, 1), (2034, 1), (2050, 1), (2147, 1), (2783, 1), (2839, -1)]

def row264 : Integer.Sparse (Fin 3237) := [(908, 1), (2034, 1), (2105, 1), (2123, 1), (2147, 2), (2839, -1)]

def row265 : Integer.Sparse (Fin 3237) := [(1873, 1), (2137, 1), (2139, 1), (2147, 2), (2749, 1), (2839, -1)]

def row266 : Integer.Sparse (Fin 3237) := [(906, 1), (2032, 1), (2075, 1), (2091, 1), (2139, 1), (2147, 1), (2839, -1)]

def row267 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (1397, -360), (1424, -360), (1568, -360), (1569, -360), (1611, -360), (1619, -360), (1896, -360), (1933, -360), (1934, -720), (2160, -360), (2370, -360), (2490, -360), (2501, -720), (2574, -360), (2575, -360), (3026, 1440), (3028, 1440), (3050, 1440), (3051, 1440), (3056, 1440), (3060, 1440), (3156, 1440), (3158, 1440), (3160, 1440), (3163, 1440), (3164, 2880), (3167, 1440), (3168, 1440), (3172, 1440), (3173, 1440), (3178, 1440), (3180, 1440), (3181, 1440), (3198, 1440)]

def row268 : Integer.Sparse (Fin 3237) := [(0, -260), (3, -40), (32, 350), (68, -160), (160, -160), (162, 160), (224, 480), (225, 160), (255, -160), (260, 120), (261, 170), (1487, 8640), (1488, 8640), (1489, 8640), (1493, 8640), (1553, 8640), (1568, 8640), (1569, 8640), (1573, 8640), (1619, 8640), (1891, 8640), (1901, 8640), (1902, 8640), (1914, 8640), (1915, 8640), (1926, 8640), (1927, 8640), (1933, 8640), (1934, 8640), (1939, 8640), (1941, 8640), (1942, 8640), (1974, 8640), (2152, 8640), (2171, 8640), (2184, 8640)]

def row269 : Integer.Sparse (Fin 3237) := [(0, -804), (3, 160), (4, 20), (32, 1040), (66, -320), (68, -640), (160, -960), (162, -640), (165, -320), (219, 960), (225, -320), (255, -320), (261, 1280), (1452, 17280), (1453, 17280), (1454, 17280), (1472, 17280), (1602, 17280), (1889, 17280), (1896, 17280), (1897, 17280), (1902, 17280), (1934, 17280), (2128, 17280), (2129, 17280), (2131, 17280), (2137, 17280), (2138, 17280), (2146, 17280), (2147, 17280), (2148, 17280), (2152, 17280), (2153, 17280), (2160, 17280), (2161, 17280), (2238, 17280)]

def row270 : Integer.Sparse (Fin 3237) := [(2367, 1), (2370, 1), (2371, 1), (2374, 1), (2492, 1), (2501, 1), (2832, -1)]

def row271 : Integer.Sparse (Fin 3237) := [(1390, 1), (1395, 1), (1397, 1), (1424, 1), (1611, 1), (2492, 1), (2832, -1)]

def row272 : Integer.Sparse (Fin 3237) := [(1611, 1), (2492, 2), (2539, 1), (2574, 1), (2575, 1), (2832, -1)]

def row273 : Integer.Sparse (Fin 3237) := [(2215, 1), (2357, 1), (2359, 1), (2374, 2), (2492, 1), (2832, -1)]

def row274 : Integer.Sparse (Fin 3237) := [(1390, 1), (2357, 1), (2466, 1), (2486, 1), (2492, 1), (2832, -1)]

def row275 : Integer.Sparse (Fin 3237) := [(2209, 1), (2367, 1), (2453, 1), (2459, 1), (2492, 2), (2832, -1)]

def row276 : Integer.Sparse (Fin 3237) := [(1395, 1), (2209, 1), (2212, 1), (2213, 1), (2215, 1), (2492, 1), (2832, -1)]

def row277 : Integer.Sparse (Fin 3237) := [(2490, 1), (2492, 1), (2501, 2), (2575, 1), (2832, -1)]

def row278 : Integer.Sparse (Fin 3237) := [(1424, 1), (2374, 1), (2459, 1), (2492, 1), (2498, 1), (2501, 1), (2832, -1)]

def row279 : Integer.Sparse (Fin 3237) := [(2213, 1), (2371, 1), (2466, 1), (2468, 1), (2492, 1), (2539, 1), (2832, -1)]

def row280 : Integer.Sparse (Fin 3237) := [(1397, 1), (2359, 1), (2453, 1), (2468, 1), (2490, 1), (2492, 1), (2832, -1)]

def row281 : Integer.Sparse (Fin 3237) := [(0, -464), (3, -80), (4, 20), (32, -440), (68, -320), (160, -1920), (162, -640), (165, -320), (225, -640), (255, -640), (256, -640), (261, 660), (768, 17280), (769, 17280), (772, 17280), (775, 17280), (844, 17280), (1363, 17280), (1374, 17280), (1404, 17280), (1555, 17280), (2011, 17280), (2013, 17280), (2016, 17280), (2065, 17280), (2067, 17280), (2088, 17280), (2107, 17280), (2112, 17280), (2128, 17280), (2135, 17280), (2145, 17280), (2147, 17280), (2157, 17280), (2182, 17280), (2498, 17280), (2704, 17280), (2720, 17280)]

def row282 : Integer.Sparse (Fin 3237) := [(0, -27), (32, -20), (160, -160), (162, -80), (225, -80), (261, 55), (1371, 2160), (1374, 2160), (1375, 2160), (1423, 2160), (1563, 2160), (2011, 2160), (2013, 2160), (2016, 2160), (2146, 2160), (2248, 2160), (2250, 2160), (2253, 2160), (2306, 2160), (2434, 2160), (2447, 2160), (2448, 2160), (2477, 2160), (2478, 2160), (2484, 2160), (2486, 2160), (2491, 2160), (2492, 2160), (2497, 2160), (2516, 2160), (2528, 2160), (2532, 2160), (2704, 2160), (2720, 2160)]

def row283 : Integer.Sparse (Fin 3237) := [(1942, 2), (2704, 2), (2720, 1), (2765, 1), (2840, -1)]

def row284 : Integer.Sparse (Fin 3237) := [(854, 1), (1827, 1), (1877, 1), (1942, 1), (1962, 1), (1973, 1), (2840, -1)]

def row285 : Integer.Sparse (Fin 3237) := [(1766, 1), (1769, 1), (1771, 1), (1784, 1), (1942, 1), (2704, 1), (2840, -1)]

def row286 : Integer.Sparse (Fin 3237) := [(0, -111), (3, -20), (4, 5), (32, -80), (159, 240), (162, 80), (165, -80), (225, 160), (261, -50), (610, 4320), (611, 4320), (612, 4320), (623, 4320), (671, 4320), (1688, 4320), (1689, 4320), (1690, 4320), (1699, 4320), (1730, 4320), (1731, 4320), (1738, 4320), (1766, 4320), (1854, 4320), (1855, 4320), (1857, 4320), (1938, 4320), (1939, 4320), (1942, 4320), (1943, 4320), (1944, 4320), (1951, 4320), (1973, 4320), (2738, 4320), (2742, 4320), (2743, 4320)]

def row287 : Integer.Sparse (Fin 3237) := [(0, -100), (32, -30), (160, -160), (225, 160), (255, -160), (256, -320), (261, -50), (1058, 8640), (1059, 8640), (1060, 8640), (1070, 8640), (1150, 8640), (2066, 8640), (2070, 8640), (2096, 8640), (2158, 8640), (2338, 8640), (2339, 8640), (2347, 8640), (2403, 8640), (2409, 8640), (2434, 8640), (2467, 8640), (2468, 8640), (2482, 8640), (2494, 8640), (2495, 8640), (2498, 8640), (2504, 8640), (2528, 8640), (2572, 8640), (2574, 8640), (2718, 8640), (2723, 8640), (2743, 8640)]

def row288 : Integer.Sparse (Fin 3237) := [(2146, 1), (2719, 1), (2723, 1), (2728, 1), (2729, 1), (2766, 1), (2840, -1)]

def row289 : Integer.Sparse (Fin 3237) := [(902, 1), (904, 1), (907, 1), (911, 1), (942, 1), (2146, 1), (2840, -1)]

def row290 : Integer.Sparse (Fin 3237) := [(911, 1), (2047, 1), (2107, 1), (2146, 1), (2157, 1), (2160, 1), (2840, -1)]

def row291 : Integer.Sparse (Fin 3237) := [(1828, 1), (1830, 1), (2120, 1), (2122, 1), (2146, 1), (2728, 1), (2840, -1)]

def row292 : Integer.Sparse (Fin 3237) := [(902, 1), (2029, 1), (2120, 1), (2144, 1), (2146, 2), (2840, -1)]

def row293 : Integer.Sparse (Fin 3237) := [(1804, 1), (1829, 1), (2104, 1), (2107, 1), (2146, 1), (2719, 1), (2840, -1)]

def row294 : Integer.Sparse (Fin 3237) := [(1812, 1), (2029, 1), (2033, 1), (2047, 1), (2146, 1), (2723, 1), (2840, -1)]

def row295 : Integer.Sparse (Fin 3237) := [(907, 1), (2033, 1), (2104, 1), (2122, 1), (2146, 1), (2148, 1), (2840, -1)]

def row296 : Integer.Sparse (Fin 3237) := [(0, -484), (3, -80), (4, 20), (32, 640), (68, -320), (160, -320), (162, 320), (165, -320), (225, 320), (261, 320), (1405, 17280), (1406, 17280), (1407, 17280), (1425, 17280), (1602, 17280), (1888, 17280), (1894, 17280), (1896, 17280), (1901, 17280), (1933, 17280), (2127, 17280), (2128, 17280), (2130, 17280), (2136, 17280), (2137, 17280), (2143, 17280), (2146, 17280), (2147, 17280), (2150, 17280), (2152, 17280), (2158, 17280), (2160, 17280), (2168, 17280), (2182, 17280), (2234, 17280), (2236, 17280)]

def row297 : Integer.Sparse (Fin 3237) := [(1814, 1), (2355, 1), (2359, 1), (2370, 1), (2490, 1), (2498, 1), (2832, -1)]

def row298 : Integer.Sparse (Fin 3237) := [(1403, 1), (1406, 1), (1408, 1), (1424, 1), (1620, 1), (2498, 1), (2832, -1)]

def row299 : Integer.Sparse (Fin 3237) := [(2207, 1), (2359, 1), (2361, 1), (2362, 1), (2374, 1), (2498, 1), (2832, -1)]

def row300 : Integer.Sparse (Fin 3237) := [(1403, 1), (1809, 1), (2361, 1), (2486, 1), (2496, 1), (2498, 1), (2832, -1)]

def row301 : Integer.Sparse (Fin 3237) := [(0, -31), (32, 25), (160, 80), (225, 40), (256, 80), (261, -140), (2289, 2160), (2290, 2160), (2292, 2160), (2300, 4320), (2407, 4320), (2436, 2160), (2437, 4320), (2444, 2160), (2487, 4320), (2489, 4320), (2493, 4320), (2496, 2160), (2500, 2160), (2501, 4320), (2523, 4320), (2526, 2160), (2535, 2160), (2698, 2160), (2725, 4320)]

def row302 : Integer.Sparse (Fin 3237) := [(2693, 1), (2737, 2), (2762, 1), (2763, 1), (2839, -1)]

def row303 : Integer.Sparse (Fin 3237) := [(796, 1), (797, 1), (802, 2), (833, 1), (2839, -1)]

def row304 : Integer.Sparse (Fin 3237) := [(833, 1), (1859, 2), (1957, 1), (1958, 1), (2839, -1)]

def row305 : Integer.Sparse (Fin 3237) := [(1743, 1), (1746, 1), (1753, 2), (2693, 1), (2839, -1)]

def row306 : Integer.Sparse (Fin 3237) := [(802, 1), (1753, 1), (1852, 1), (1932, 1), (1934, 1), (2839, -1)]

def row307 : Integer.Sparse (Fin 3237) := [(1847, 1), (1849, 1), (1852, 1), (1859, 1), (2737, 1), (2839, -1)]

def row308 : Integer.Sparse (Fin 3237) := [(797, 1), (1746, 1), (1849, 2), (1924, 1), (2839, -1)]

def row309 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (1388, -180), (1420, -180), (1548, -180), (1549, -180), (1592, -180), (1610, -180), (1913, -180), (1933, -360), (1934, -720), (2177, -180), (2456, -180), (2490, -360), (2501, -720), (2573, -180), (2575, -360), (3026, 1440), (3155, 720), (3156, 720), (3158, 1440), (3168, 720), (3169, 720), (3170, 720), (3172, 1440), (3173, 1440), (3180, 1440), (3190, 720)]

def row310 : Integer.Sparse (Fin 3237) := [(0, -222), (3, 20), (32, 255), (68, 80), (224, -240), (255, 160), (260, -60), (261, 265), (1548, 4320), (1549, 4320), (1553, 8640), (1592, 4320), (1888, 4320), (1889, 4320), (1891, 8640), (1923, 4320), (1924, 4320), (1926, 8640), (1927, 8640), (1933, 8640), (1934, 8640), (1941, 8640), (1958, 4320), (2137, 4320)]

def row311 : Integer.Sparse (Fin 3237) := [(0, -688), (3, -120), (4, 20), (32, 920), (66, 160), (68, 480), (160, 160), (162, 640), (165, 320), (219, -480), (225, 160), (261, 780), (1913, 8640), (1915, 8640), (1934, 17280), (2128, 17280), (2129, 17280), (2131, 17280), (2147, 17280), (2168, 8640), (2169, 8640), (2171, 8640), (2172, 8640), (2177, 8640), (2178, 8640), (2238, 17280)]

def row312 : Integer.Sparse (Fin 3237) := [(2456, 1), (2459, 1), (2501, 2), (2832, -1)]

def row313 : Integer.Sparse (Fin 3237) := [(1388, 1), (1390, 2), (1420, 1), (1610, 1), (2832, -1)]

def row314 : Integer.Sparse (Fin 3237) := [(1610, 1), (2535, 1), (2573, 1), (2575, 2), (2832, -1)]

def row315 : Integer.Sparse (Fin 3237) := [(2355, 1), (2357, 2), (2367, 1), (2459, 1), (2832, -1)]

def row316 : Integer.Sparse (Fin 3237) := [(1420, 1), (2367, 1), (2496, 1), (2501, 2), (2832, -1)]

def row317 : Integer.Sparse (Fin 3237) := [(2464, 1), (2466, 2), (2535, 1), (2832, -1)]

def row318 : Integer.Sparse (Fin 3237) := [(1388, 1), (2355, 1), (2464, 1), (2490, 2), (2832, -1)]

def row319 : Integer.Sparse (Fin 3237) := [(0, -31), (32, 75), (160, 720), (162, 320), (225, 160), (256, 160), (261, -210), (1366, 4320), (1369, 8640), (1419, 4320), (1559, 4320), (2288, 4320), (2290, 4320), (2298, 8640), (2444, 4320), (2445, 8640), (2489, 8640), (2493, 8640), (2494, 8640), (2496, 8640), (2526, 4320), (2529, 8640), (2531, 4320), (2702, 4320), (2719, 8640)]

def row320 : Integer.Sparse (Fin 3237) := [(1924, 1), (2694, 1), (2738, 2), (2760, 1), (2762, 1), (2839, -1)]

def row321 : Integer.Sparse (Fin 3237) := [(834, 1), (1860, 2), (1924, 1), (1952, 1), (1957, 1), (2839, -1)]

def row322 : Integer.Sparse (Fin 3237) := [(1744, 1), (1746, 1), (1756, 2), (1924, 1), (2694, 1), (2839, -1)]

def row323 : Integer.Sparse (Fin 3237) := [(805, 1), (1756, 1), (1854, 1), (1924, 2), (1932, 1), (2839, -1)]

def row324 : Integer.Sparse (Fin 3237) := [(1848, 1), (1849, 1), (1854, 1), (1860, 1), (1924, 1), (2738, 1), (2839, -1)]

def row325 : Integer.Sparse (Fin 3237) := [(1922, 1), (1924, 3), (1952, 1), (2760, 1), (2839, -1)]

def row326 : Integer.Sparse (Fin 3237) := [(0, 33), (32, -5), (160, 80), (225, 80), (261, 190), (2081, -8640), (2177, -4320), (2555, -8640), (2573, -4320), (2717, -8640), (2722, -8640), (2763, -4320), (2895, 17280), (2896, 17280), (2897, 34560), (2910, 17280), (3089, 17280), (3090, 17280), (3091, 34560), (3122, 34560), (3123, 34560), (3125, 34560), (3169, 17280), (3171, 17280), (3174, 34560), (3175, 34560), (3189, 17280), (3228, 17280)]

def row327 : Integer.Sparse (Fin 3237) := [(0, -125), (3, -160), (4, 20), (32, 210), (66, 320), (68, 160), (71, 160), (159, -480), (160, 1200), (162, 240), (165, 160), (225, 480), (255, 160), (256, 320), (261, -445), (595, 4320), (596, 4320), (601, 8640), (635, 4320), (1678, 4320), (1679, 4320), (1682, 8640), (1801, 8640), (1803, 8640), (1811, 8640), (1923, 4320), (1925, 4320), (1930, 8640), (1935, 8640), (1957, 4320), (2780, 4320)]

def row328 : Integer.Sparse (Fin 3237) := [(0, -33), (32, 5), (160, -80), (225, -80), (261, -190), (1055, 4320), (1056, 8640), (1062, 4320), (1148, 4320), (2336, 4320), (2337, 8640), (2341, 4320), (2464, 4320), (2465, 8640), (2476, 8640), (2477, 8640), (2479, 8640), (2497, 8640), (2500, 4320), (2526, 4320), (2555, 8640), (2573, 4320), (2722, 8640), (2740, 4320)]

def row329 : Integer.Sparse (Fin 3237) := [(2168, 1), (2717, 2), (2724, 1), (2763, 1), (2839, -1)]

def row330 : Integer.Sparse (Fin 3237) := [(920, 1), (921, 1), (923, 1), (931, 2), (2168, 1), (2839, -1)]

def row331 : Integer.Sparse (Fin 3237) := [(923, 1), (2081, 2), (2168, 1), (2175, 1), (2177, 1), (2839, -1)]

def row332 : Integer.Sparse (Fin 3237) := [(1816, 1), (2124, 1), (2125, 2), (2168, 1), (2724, 1), (2839, -1)]

def row333 : Integer.Sparse (Fin 3237) := [(1801, 1), (2074, 1), (2081, 1), (2088, 1), (2168, 1), (2717, 1), (2839, -1)]

def row334 : Integer.Sparse (Fin 3237) := [(921, 1), (2074, 2), (2124, 1), (2168, 1), (2169, 1), (2839, -1)]

def row335 : Integer.Sparse (Fin 3237) := [(0, -207), (3, 20), (4, -10), (32, 265), (68, 80), (160, 320), (162, 80), (165, 160), (261, 330), (1913, 4320), (1914, 4320), (1933, 8640), (2127, 8640), (2128, 8640), (2130, 8640), (2146, 8640), (2167, 4320), (2170, 4320), (2171, 4320), (2176, 4320), (2177, 4320), (2182, 8640), (2234, 8640), (2235, 4320)]

def row336 : Integer.Sparse (Fin 3237) := [(2453, 1), (2456, 1), (2490, 2), (2496, 1), (2832, -1)]

def row337 : Integer.Sparse (Fin 3237) := [(1402, 1), (1403, 2), (1420, 1), (1618, 1), (2496, 1), (2832, -1)]

def row338 : Integer.Sparse (Fin 3237) := [(1618, 1), (1947, 1), (2496, 1), (2573, 1), (2578, 2), (2832, -1)]

def row339 : Integer.Sparse (Fin 3237) := [(0, 61), (32, 15), (160, -240), (225, 80), (261, 390), (866, -2160), (869, -720), (1473, -2160), (1622, -720), (1628, -2160), (1630, -720), (1632, -720), (2097, -4320), (2160, -2160), (2315, -2160), (2321, -720), (2556, -4320), (2563, -2160), (2571, -2160), (2574, -2160), (2766, -2160)]

def row340 : Integer.Sparse (Fin 3237) := [(0, -19), (32, -5), (160, 80), (261, -110), (866, 720), (869, 240), (1473, 720), (1622, 240), (2097, 1440), (2160, 720)]

def row341 : Integer.Sparse (Fin 3237) := [(0, 57), (32, 10), (160, -160), (256, 80), (261, -95), (695, -2160), (697, -720), (700, -720), (1165, -2160), (1167, -720), (1179, -720), (1784, -4320), (1786, -2160), (1789, -2160), (1908, -2160), (1979, -2160), (1980, -1440), (2447, -4320), (2451, -2160), (2538, -2160), (2578, -2160), (2580, -720), (2769, -2160)]

def row342 : Integer.Sparse (Fin 3237) := [(0, -5), (32, -1), (160, 16), (261, 8), (695, 216), (697, 72), (700, 72), (1784, 432), (1786, 216), (1789, 216), (1979, 216), (1980, 72)]

def row343 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (261, -40), (1611, -2160), (1619, -2160), (1622, -720), (1632, -720), (1950, -2160), (1969, -2160), (1980, -1440), (2503, -2160), (2537, -2160), (2578, -2160), (3175, 17280), (3185, 8640), (3195, 8640), (3200, 2880)]

def row344 : Integer.Sparse (Fin 3237) := [(0, -19), (32, 25), (160, 80), (261, 40), (1611, 1080), (1632, 360), (1935, 2160), (1950, 1080), (1951, 1080), (1970, 1080), (1981, 360)]

def row345 : Integer.Sparse (Fin 3237) := [(0, -19), (32, 25), (160, 80), (261, 40), (1969, 720), (1975, 720), (1980, 240), (1981, 240), (2182, 1440), (2187, 720)]

def row346 : Integer.Sparse (Fin 3237) := [(1980, 1), (2537, 3), (2579, 1), (2832, -1)]

def row347 : Integer.Sparse (Fin 3237) := [(2578, 3), (2579, 1), (2832, -1)]

def row348 : Integer.Sparse (Fin 3237) := [(2503, 3), (2579, 1), (2832, -1)]

def row349 : Integer.Sparse (Fin 3237) := [(0, -9), (32, -10), (160, -80), (162, -80), (261, -25), (696, 2160), (698, 720), (699, 720), (1785, 4320), (1787, 2160), (1788, 2160), (1965, 2160), (1975, 2160), (1977, 720), (1980, 720), (2187, 2160)]

def row350 : Integer.Sparse (Fin 3237) := [(870, 3), (872, 1), (873, 1), (1981, 1), (2832, -1)]

def row351 : Integer.Sparse (Fin 3237) := [(870, 1), (1494, 1), (1840, 2), (1978, 1), (1981, 1), (2832, -1)]

def row352 : Integer.Sparse (Fin 3237) := [(873, 1), (1842, 3), (1980, 1), (1981, 1), (2832, -1)]

def row353 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 5), (261, -10), (826, -180), (828, -90), (832, -90), (1758, -180), (1786, -90), (2050, -180), (2055, -90), (2087, -180), (2309, -180), (2310, -90), (2311, -90), (2319, -90), (2449, -180), (2451, -90), (2557, -180), (2561, -180), (2569, -180), (2570, -180), (2575, -180), (2577, -90), (2578, -90), (2580, -90), (2764, -180), (2769, -90)]

def row354 : Integer.Sparse (Fin 3237) := [(0, -11), (32, -5), (261, 10), (826, 180), (828, 90), (832, 90), (1758, 180), (1786, 90), (2050, 180), (2055, 90), (2087, 180)]

def row355 : Integer.Sparse (Fin 3237) := [(0, 49), (32, 15), (261, 50), (654, -720), (656, -360), (663, -360), (693, -360), (1156, -720), (1157, -360), (1158, -360), (1177, -360), (1753, -720), (1755, -720), (1761, -720), (1782, -720), (1934, -720), (1936, -360), (1950, -360), (2437, -720), (2438, -720), (2439, -720), (2450, -720), (2501, -720), (2502, -360), (2503, -360), (2557, -720), (2558, -360), (2565, -360), (2570, -720), (2571, -360), (2575, -360), (2803, -720)]

def row356 : Integer.Sparse (Fin 3237) := [(0, -3), (32, -1), (261, -2), (654, 48), (656, 24), (663, 24), (693, 24), (1753, 48), (1755, 48), (1761, 48), (1782, 48), (1934, 48), (1936, 24), (1950, 24)]

def row357 : Integer.Sparse (Fin 3237) := [(0, 67), (32, -85), (160, -80), (261, -100), (1592, -4320), (1610, -4320), (1611, -2160), (1619, -2160), (1933, -4320), (1934, -8640), (1950, -2160), (1969, -2160), (2160, -2160), (2177, -4320), (2490, -4320), (2501, -8640), (2503, -2160), (2537, -2160), (2573, -4320), (2574, -2160), (2575, -4320), (2578, -2160), (3180, 17280), (3190, 17280), (3198, 8640)]

def row358 : Integer.Sparse (Fin 3237) := [(0, -4), (32, 5), (261, 5), (1592, 120), (1619, 60), (1933, 120), (1934, 120), (1941, 120), (1958, 120), (1969, 60), (1974, 60)]

def row359 : Integer.Sparse (Fin 3237) := [(0, -4), (32, 5), (261, 5), (1934, 90), (1950, 45), (2147, 90), (2160, 45), (2161, 45), (2177, 90), (2178, 90)]

def row360 : Integer.Sparse (Fin 3237) := [(2501, 2), (2503, 1), (2575, 1), (2832, -1)]

def row361 : Integer.Sparse (Fin 3237) := [(1610, 2), (1611, 1), (2575, 1), (2832, -1)]

def row362 : Integer.Sparse (Fin 3237) := [(2575, 3), (2832, -1)]

def row363 : Integer.Sparse (Fin 3237) := [(2503, 1), (2535, 2), (2537, 1), (2539, 1), (2575, 1), (2832, -1)]

def row364 : Integer.Sparse (Fin 3237) := [(2490, 2), (2537, 1), (2575, 1), (2832, -1)]

def row365 : Integer.Sparse (Fin 3237) := [(0, 233), (32, 75), (160, 240), (225, -80), (261, -90), (822, -4320), (825, -2160), (832, -2160), (1394, -4320), (1426, -2160), (1577, -4320), (1579, -2160), (1580, -2160), (1595, -2160), (1631, -2160), (2047, -4320), (2055, -2160), (2081, -4320), (2087, -4320), (2177, -4320), (2303, -4320), (2311, -2160), (2318, -2160), (2555, -4320), (2561, -4320), (2562, -4320), (2570, -4320), (2572, -4320), (2573, -4320), (2575, -2160), (2577, -2160), (2578, -2160), (2765, -4320), (2766, -2160)]

def row366 : Integer.Sparse (Fin 3237) := [(0, -71), (32, -25), (160, -80), (261, 50), (822, 1440), (825, 720), (832, 720), (1394, 1440), (1426, 720), (1595, 720), (2047, 1440), (2055, 720), (2081, 1440), (2087, 1440), (2177, 1440)]

def row367 : Integer.Sparse (Fin 3237) := [(0, 236), (32, 75), (160, 240), (256, -80), (261, -165), (657, -4320), (659, -2160), (662, -2160), (695, -2160), (1163, -4320), (1164, -2160), (1165, -2160), (1176, -2160), (1756, -4320), (1758, -4320), (1760, -4320), (1784, -4320), (1968, -4320), (1969, -2160), (1979, -2160), (2445, -4320), (2446, -4320), (2447, -4320), (2449, -4320), (2536, -4320), (2537, -2160), (2538, -2160), (2562, -4320), (2563, -2160), (2564, -2160), (2578, -4320), (2579, -2160), (2580, -2160), (2764, -4320)]

def row368 : Integer.Sparse (Fin 3237) := [(0, -71), (32, -25), (160, -80), (261, 50), (657, 1440), (659, 720), (662, 720), (695, 720), (1756, 1440), (1758, 1440), (1760, 1440), (1784, 1440), (1968, 1440), (1969, 720), (1979, 720)]

def row369 : Integer.Sparse (Fin 3237) := [(0, 77), (32, -95), (160, 80), (261, -80), (1593, -4320), (1611, -2160), (1618, -4320), (1619, -2160), (1620, -4320), (1933, -4320), (1934, -4320), (1949, -4320), (2160, -2160), (2177, -4320), (2490, -4320), (2501, -4320), (2573, -4320), (2574, -2160), (2575, -2160), (2578, -4320), (2579, -2160), (3170, 17280), (3175, 17280), (3181, 17280), (3184, 17280), (3185, 8640), (3195, 8640)]

def row370 : Integer.Sparse (Fin 3237) := [(0, -53), (32, 65), (160, -80), (261, 50), (1593, 1440), (1611, 720), (1620, 720), (1924, 1440), (1934, 1440), (1935, 1440), (1942, 1440), (1959, 1440), (1970, 720), (1975, 720)]

def row371 : Integer.Sparse (Fin 3237) := [(0, -45), (32, -5), (160, 240), (255, 160), (256, 160), (261, 60), (816, 4320), (818, 2160), (831, 2160), (864, 2160), (1083, 4320), (1095, 2160), (1151, 2160), (2041, 4320), (2054, 2160), (2078, 4320), (2086, 4320), (2096, 4320), (2134, 4320), (2158, 2160), (2186, 4320), (2528, 4320), (2539, 2160), (2574, 2160)]

def row372 : Integer.Sparse (Fin 3237) := [(0, -29), (32, 5), (160, 160), (162, 80), (225, 80), (256, 80), (261, -10), (682, 4320), (684, 2160), (688, 2160), (694, 2160), (1772, 4320), (1774, 4320), (1778, 4320), (1783, 4320), (1904, 4320), (1906, 2160), (1910, 2160), (1944, 4320), (1946, 2160), (1951, 2160), (1973, 4320), (1974, 2160), (2527, 4320), (2537, 2160), (2538, 2160)]

def row373 : Integer.Sparse (Fin 3237) := [(1970, 1), (2157, 2), (2160, 1), (2161, 1), (2769, 1), (2840, -1)]

def row374 : Integer.Sparse (Fin 3237) := [(848, 2), (850, 1), (851, 1), (871, 1), (1970, 1), (2840, -1)]

def row375 : Integer.Sparse (Fin 3237) := [(848, 1), (1823, 1), (1872, 1), (1963, 1), (1967, 1), (1970, 1), (2840, -1)]

def row376 : Integer.Sparse (Fin 3237) := [(946, 1), (1823, 1), (1825, 1), (1841, 1), (1970, 1), (2157, 1), (2840, -1)]

def row377 : Integer.Sparse (Fin 3237) := [(949, 1), (1872, 2), (1874, 1), (1970, 1), (2161, 1), (2840, -1)]

def row378 : Integer.Sparse (Fin 3237) := [(851, 1), (1825, 2), (1874, 1), (1969, 1), (1970, 1), (2840, -1)]

def row379 : Integer.Sparse (Fin 3237) := [(850, 1), (946, 2), (948, 1), (949, 1), (1970, 1), (2840, -1)]

def row380 : Integer.Sparse (Fin 3237) := [(0, -64), (32, -40), (160, 320), (255, 160), (256, 160), (261, -200), (1100, 8640), (1101, 4320), (1105, 4320), (1171, 4320), (1607, 8640), (1628, 4320), (1631, 4320), (1832, 8640), (1842, 4320), (1929, 8640), (1944, 8640), (1947, 8640), (1965, 4320), (1966, 8640), (1967, 8640), (1978, 4320), (1979, 4320), (2185, 8640), (2190, 4320)]

def row381 : Integer.Sparse (Fin 3237) := [(2187, 1), (2527, 2), (2538, 2), (2571, 1), (2831, -1)]

def row382 : Integer.Sparse (Fin 3237) := [(935, 2), (938, 1), (940, 1), (951, 1), (2187, 1), (2831, -1)]

def row383 : Integer.Sparse (Fin 3237) := [(935, 1), (2096, 1), (2115, 1), (2176, 1), (2185, 1), (2187, 1), (2831, -1)]

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

def row384 : Integer.Sparse (Fin 3237) := [(1451, 1), (2100, 1), (2115, 1), (2119, 1), (2187, 1), (2527, 1), (2831, -1)]

def row385 : Integer.Sparse (Fin 3237) := [(951, 1), (2119, 2), (2187, 2), (2190, 1), (2831, -1)]

def row386 : Integer.Sparse (Fin 3237) := [(1473, 1), (2096, 2), (2102, 1), (2187, 1), (2538, 1), (2831, -1)]

def row387 : Integer.Sparse (Fin 3237) := [(940, 1), (2100, 2), (2102, 2), (2187, 1), (2831, -1)]

def row388 : Integer.Sparse (Fin 3237) := [(0, -49), (32, 80), (160, -80), (162, 80), (261, 65), (1785, 4320), (1787, 2160), (1788, 2160), (1931, 4320), (1946, 2160), (1949, 2160), (1980, 2160), (1981, 2160), (2143, 4320), (2155, 2160), (2158, 2160), (2167, 4320), (2173, 4320), (2176, 4320), (2182, 4320), (2187, 4320), (2214, 4320), (2217, 2160)]

def row389 : Integer.Sparse (Fin 3237) := [(864, 1), (1835, 2), (1949, 1), (1978, 1), (1980, 1), (2832, -1)]

def row390 : Integer.Sparse (Fin 3237) := [(1492, 2), (1494, 1), (1497, 1), (1619, 1), (1978, 1), (2832, -1)]

def row391 : Integer.Sparse (Fin 3237) := [(0, -124), (160, 640), (225, 320), (255, 160), (256, 160), (261, -100), (779, 8640), (781, 4320), (782, 4320), (867, 4320), (1689, 8640), (1701, 4320), (1943, 4320), (2017, 8640), (2018, 4320), (2069, 8640), (2070, 8640), (2098, 8640), (2147, 8640), (2157, 8640), (2158, 4320), (2539, 4320), (2743, 8640)]

def row392 : Integer.Sparse (Fin 3237) := [(0, -15), (32, -5), (160, 80), (225, 80), (261, -50), (1699, 2160), (1701, 1080), (1702, 1080), (1951, 1080), (2017, 2160), (2018, 1080), (2161, 1080), (2256, 2160), (2257, 1080), (2316, 1080), (2347, 2160), (2492, 2160), (2503, 1080), (2504, 1080), (2514, 2160), (2520, 2160), (2528, 2160), (2538, 1080), (2743, 2160)]

def row393 : Integer.Sparse (Fin 3237) := [(1974, 2), (2728, 2), (2766, 2), (2840, -1)]

def row394 : Integer.Sparse (Fin 3237) := [(867, 1), (1838, 2), (1950, 1), (1974, 1), (1979, 1), (2840, -1)]

def row395 : Integer.Sparse (Fin 3237) := [(0, -240), (3, 80), (32, -80), (159, -960), (160, 640), (162, 320), (225, 320), (256, 320), (261, 80), (274, -960), (667, 17280), (668, 8640), (676, 8640), (688, 8640), (1763, 17280), (1764, 17280), (1771, 17280), (1778, 17280), (1869, 17280), (1871, 8640), (1902, 17280), (1903, 8640), (1910, 8640), (1973, 17280), (1978, 8640), (2747, 17280), (2750, 8640)]

def row396 : Integer.Sparse (Fin 3237) := [(0, -28), (32, -15), (160, 80), (252, -240), (256, 80), (261, -15), (1093, 4320), (1095, 2160), (1096, 2160), (1166, 2160), (2041, 4320), (2054, 2160), (2187, 2160), (2364, 4320), (2374, 4320), (2375, 2160), (2417, 4320), (2448, 4320), (2528, 4320), (2533, 4320), (2534, 2160), (2574, 2160), (2577, 2160), (2784, 4320), (2787, 2160)]

def row397 : Integer.Sparse (Fin 3237) := [(2161, 1), (2748, 2), (2750, 1), (2769, 1), (2787, 1), (2840, -1)]

def row398 : Integer.Sparse (Fin 3237) := [(912, 2), (917, 1), (919, 1), (949, 1), (2161, 1), (2840, -1)]

def row399 : Integer.Sparse (Fin 3237) := [(912, 1), (2048, 1), (2108, 1), (2152, 1), (2157, 1), (2161, 1), (2840, -1)]

def row400 : Integer.Sparse (Fin 3237) := [(1872, 1), (2037, 1), (2108, 1), (2112, 1), (2161, 1), (2748, 1), (2840, -1)]

def row401 : Integer.Sparse (Fin 3237) := [(2048, 2), (2052, 1), (2055, 1), (2161, 1), (2787, 1), (2840, -1)]

def row402 : Integer.Sparse (Fin 3237) := [(919, 1), (2055, 1), (2112, 2), (2160, 1), (2161, 1), (2840, -1)]

def row403 : Integer.Sparse (Fin 3237) := [(1874, 1), (2152, 2), (2154, 1), (2161, 1), (2750, 1), (2840, -1)]

def row404 : Integer.Sparse (Fin 3237) := [(0, -138), (32, 160), (160, 320), (162, 160), (224, -480), (225, 160), (260, -120), (261, 130), (1489, 8640), (1490, 4320), (1497, 4320), (1599, 8640), (1617, 4320), (1619, 4320), (1623, 4320), (1865, 8640), (1874, 4320), (1926, 8640), (1939, 8640), (1941, 8640), (1958, 8640), (1962, 8640), (1969, 4320), (1971, 4320), (2184, 8640)]

def row405 : Integer.Sparse (Fin 3237) := [(2054, 1), (2371, 2), (2376, 1), (2503, 1), (2539, 1), (2832, -1)]

def row406 : Integer.Sparse (Fin 3237) := [(1469, 2), (1474, 1), (1476, 1), (1611, 1), (2539, 1), (2832, -1)]

def row407 : Integer.Sparse (Fin 3237) := [(1469, 1), (2049, 1), (2466, 1), (2532, 1), (2535, 1), (2539, 1), (2832, -1)]

def row408 : Integer.Sparse (Fin 3237) := [(1474, 1), (2053, 1), (2213, 2), (2217, 1), (2539, 1), (2832, -1)]

def row409 : Integer.Sparse (Fin 3237) := [(2049, 2), (2053, 1), (2054, 1), (2162, 1), (2539, 1), (2832, -1)]

def row410 : Integer.Sparse (Fin 3237) := [(1476, 1), (2162, 1), (2468, 2), (2537, 1), (2539, 1), (2832, -1)]

def row411 : Integer.Sparse (Fin 3237) := [(0, 33), (32, 10), (160, -160), (225, -80), (256, -80), (261, 25), (1786, -2160), (2047, -4320), (2055, -2160), (2451, -2160), (2572, -4320), (2577, -2160), (2699, -4320), (2703, -4320), (2766, -2160), (2769, -2160), (2928, 17280), (2929, 8640), (2931, 8640), (2937, 8640), (3113, 17280), (3114, 17280), (3115, 17280), (3119, 17280), (3181, 17280), (3182, 8640), (3185, 8640), (3195, 8640), (3197, 17280), (3198, 8640)]

def row412 : Integer.Sparse (Fin 3237) := [(0, -55), (32, -40), (160, -80), (162, -80), (225, -80), (261, 95), (671, 2160), (672, 1080), (676, 1080), (694, 1080), (1766, 2160), (1767, 2160), (1771, 2160), (1783, 2160), (1942, 2160), (1943, 1080), (1951, 1080), (1973, 2160), (1974, 1080), (1978, 1080)]

def row413 : Integer.Sparse (Fin 3237) := [(0, -33), (32, -10), (160, 160), (225, 80), (256, 80), (261, -25), (1150, 4320), (1151, 2160), (1159, 2160), (1166, 2160), (2134, 4320), (2158, 2160), (2187, 2160), (2434, 4320), (2440, 4320), (2448, 4320), (2451, 2160), (2498, 4320), (2504, 2160), (2528, 4320), (2539, 2160), (2572, 4320), (2577, 2160), (2699, 4320)]

def row414 : Integer.Sparse (Fin 3237) := [(2160, 1), (2703, 2), (2766, 1), (2769, 1), (2840, -1)]

def row415 : Integer.Sparse (Fin 3237) := [(911, 2), (916, 1), (919, 1), (948, 1), (2160, 1), (2840, -1)]

def row416 : Integer.Sparse (Fin 3237) := [(1767, 1), (1963, 1), (2107, 1), (2112, 1), (2160, 1), (2703, 1), (2840, -1)]

def row417 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -55), (160, -80), (261, -70), (1611, -2160), (1619, -2160), (1620, -4320), (1789, -2160), (1896, -4320), (1908, -2160), (1909, -2160), (2177, -4320), (2370, -4320), (2376, -2160), (2573, -4320), (2575, -2160), (2578, -2160), (3060, 17280), (3061, 8640), (3062, 8640), (3065, 17280), (3066, 8640), (3119, 17280), (3173, 17280), (3180, 17280), (3181, 17280), (3185, 8640), (3192, 17280), (3198, 8640)]

def row418 : Integer.Sparse (Fin 3237) := [(0, -70), (32, 125), (160, 160), (162, 240), (225, 80), (261, 95), (1602, 4320), (1603, 2160), (1612, 2160), (1621, 2160), (1896, 4320), (1908, 2160), (1909, 2160), (2128, 4320), (2134, 4320), (2135, 4320), (2146, 4320), (2147, 4320), (2158, 2160), (2161, 2160), (2177, 4320), (2241, 4320)]

def row419 : Integer.Sparse (Fin 3237) := [(0, -67), (32, 15), (160, -240), (225, -160), (256, -160), (261, -90), (1692, 4320), (1693, 4320), (1697, 8640), (1947, 4320), (2292, 4320), (2293, 4320), (2304, 8640), (2341, 4320), (2345, 8640), (2500, 4320), (2501, 8640), (2517, 8640), (2523, 8640), (2526, 4320), (2533, 8640), (2536, 8640), (2740, 4320), (2748, 8640)]

def row420 : Integer.Sparse (Fin 3237) := [(1958, 1), (2724, 1), (2747, 2), (2763, 1), (2768, 1), (2839, -1)]

def row421 : Integer.Sparse (Fin 3237) := [(833, 1), (835, 1), (838, 1), (845, 2), (1958, 1), (2839, -1)]

def row422 : Integer.Sparse (Fin 3237) := [(1816, 1), (1817, 1), (1820, 2), (1958, 1), (2724, 1), (2839, -1)]

def row423 : Integer.Sparse (Fin 3237) := [(845, 1), (1820, 1), (1869, 1), (1934, 1), (1958, 1), (1968, 1), (2839, -1)]

def row424 : Integer.Sparse (Fin 3237) := [(1859, 1), (1861, 1), (1863, 1), (1869, 1), (1958, 1), (2747, 1), (2839, -1)]

def row425 : Integer.Sparse (Fin 3237) := [(838, 1), (1817, 1), (1863, 2), (1958, 1), (1959, 1), (2839, -1)]

def row426 : Integer.Sparse (Fin 3237) := [(0, 49), (32, -5), (160, 80), (256, 160), (261, -50), (2087, -8640), (2177, -4320), (2561, -8640), (2573, -4320), (2749, -8640), (2783, -8640), (2786, -8640), (2794, -4320), (2908, 17280), (2909, 17280), (2915, 17280), (2919, 34560), (3102, 17280), (3105, 17280), (3107, 34560), (3129, 34560), (3131, 34560), (3136, 34560), (3156, 17280), (3157, 17280), (3160, 34560), (3189, 17280), (3194, 34560)]

def row427 : Integer.Sparse (Fin 3237) := [(0, -334), (3, 240), (32, -160), (66, -320), (71, -320), (159, 960), (160, -1120), (162, -160), (225, -160), (256, -640), (261, 190), (274, 960), (633, 8640), (634, 8640), (640, 8640), (650, 17280), (1742, 8640), (1746, 8640), (1751, 17280), (1820, 17280), (1822, 17280), (1838, 17280), (1889, 8640), (1890, 8640), (1897, 17280), (1957, 8640), (1967, 17280), (2749, 8640)]

def row428 : Integer.Sparse (Fin 3237) := [(0, -57), (32, 25), (160, -240), (225, -160), (252, 240), (256, -160), (261, -50), (1086, 4320), (1087, 4320), (1090, 8640), (1162, 4320), (2367, 4320), (2368, 4320), (2371, 8640), (2413, 4320), (2415, 8640), (2444, 4320), (2488, 8640), (2517, 8640), (2520, 8640), (2526, 4320), (2527, 8640), (2561, 8640), (2573, 4320), (2786, 8640)]

def row429 : Integer.Sparse (Fin 3237) := [(2178, 1), (2749, 1), (2783, 2), (2794, 1), (2839, -1)]

def row430 : Integer.Sparse (Fin 3237) := [(924, 1), (928, 1), (930, 1), (937, 2), (2178, 1), (2839, -1)]

def row431 : Integer.Sparse (Fin 3237) := [(924, 1), (2082, 2), (2171, 1), (2175, 1), (2178, 1), (2839, -1)]

def row432 : Integer.Sparse (Fin 3237) := [(2025, 1), (2114, 1), (2117, 2), (2178, 1), (2839, -1)]

def row433 : Integer.Sparse (Fin 3237) := [(937, 1), (2098, 1), (2117, 1), (2178, 1), (2184, 1), (2186, 1), (2839, -1)]

def row434 : Integer.Sparse (Fin 3237) := [(2032, 1), (2082, 1), (2087, 1), (2098, 1), (2178, 1), (2783, 1), (2839, -1)]

def row435 : Integer.Sparse (Fin 3237) := [(930, 1), (2087, 2), (2114, 1), (2177, 1), (2178, 1), (2839, -1)]

def row436 : Integer.Sparse (Fin 3237) := [(2139, 1), (2171, 1), (2178, 1), (2184, 2), (2749, 1), (2839, -1)]

def row437 : Integer.Sparse (Fin 3237) := [(928, 1), (2025, 1), (2032, 2), (2139, 1), (2178, 1), (2839, -1)]

def row438 : Integer.Sparse (Fin 3237) := [(0, -456), (32, 590), (160, 160), (162, -160), (224, 480), (225, -160), (260, 120), (261, 710), (1582, 8640), (1590, 8640), (1592, 8640), (1599, 17280), (1864, 8640), (1865, 17280), (1873, 8640), (1923, 8640), (1926, 17280), (1952, 8640), (1955, 8640), (1958, 17280), (1962, 17280), (1969, 17280), (1974, 17280)]

def row439 : Integer.Sparse (Fin 3237) := [(2045, 1), (2460, 1), (2503, 2), (2535, 1), (2832, -1)]

def row440 : Integer.Sparse (Fin 3237) := [(1465, 1), (1467, 1), (1469, 2), (1610, 1), (2535, 1), (2832, -1)]

def row441 : Integer.Sparse (Fin 3237) := [(1465, 1), (2043, 1), (2531, 1), (2535, 3), (2832, -1)]

def row442 : Integer.Sparse (Fin 3237) := [(2043, 1), (2045, 1), (2049, 2), (2156, 1), (2535, 1), (2832, -1)]

def row443 : Integer.Sparse (Fin 3237) := [(1467, 1), (2156, 1), (2464, 1), (2535, 1), (2537, 2), (2832, -1)]

def row444 : Integer.Sparse (Fin 3237) := [(0, 195), (32, 5), (160, -80), (225, -80), (261, -130), (790, -2160), (792, -2160), (795, -2160), (822, -4320), (1294, -2160), (1306, -4320), (1325, -2160), (1327, -2160), (1328, -4320), (1595, -2160), (1631, -2160), (2023, -4320), (2024, -4320), (2047, -4320), (2073, -2160), (2081, -4320), (2177, -4320), (2291, -2160), (2294, -2160), (2303, -4320), (2555, -4320), (2559, -2160), (2568, -4320), (2570, -4320), (2572, -4320), (2573, -4320), (2576, -4320), (2578, -4320), (2694, -2160), (2699, -4320), (2702, -2160), (2703, -4320)]

def row445 : Integer.Sparse (Fin 3237) := [(0, -140), (32, -5), (160, 80), (225, 40), (261, 115), (790, 2160), (792, 2160), (795, 2160), (822, 4320), (1294, 2160), (1306, 4320), (1595, 2160), (2023, 4320), (2024, 4320), (2047, 4320), (2073, 2160), (2081, 4320), (2177, 4320), (2694, 2160), (2699, 4320)]

def row446 : Integer.Sparse (Fin 3237) := [(0, 41), (32, -5), (160, 80), (225, 40), (256, 80), (261, 70), (1758, -4320), (2081, -4320), (2087, -4320), (2097, -4320), (2449, -4320), (2555, -4320), (2556, -4320), (2561, -4320), (2693, -2160), (2698, -2160), (2763, -2160), (2794, -2160), (2910, 8640), (2911, 8640), (2915, 8640), (2920, 17280), (3103, 8640), (3105, 8640), (3108, 17280), (3170, 8640), (3171, 8640), (3175, 17280), (3189, 8640), (3190, 8640), (3194, 17280)]

def row447 : Integer.Sparse (Fin 3237) := [(0, -78), (32, 35), (160, 160), (162, 80), (225, 80), (261, -235), (635, 1440), (636, 1440), (640, 1440), (655, 2880), (1743, 1440), (1746, 1440), (1754, 2880), (1924, 1440), (1925, 1440), (1935, 2880), (1957, 1440), (1958, 1440), (1967, 2880)]

def row448 : Integer.Sparse (Fin 3237) := [(0, -41), (32, 5), (160, -80), (225, -40), (256, -80), (261, -70), (1148, 2160), (1149, 4320), (1155, 2160), (1162, 2160), (2433, 4320), (2436, 2160), (2444, 2160), (2449, 4320), (2496, 2160), (2497, 4320), (2500, 2160), (2526, 2160), (2527, 4320), (2535, 2160), (2555, 4320), (2556, 4320), (2561, 4320), (2698, 2160)]

def row449 : Integer.Sparse (Fin 3237) := [(2177, 1), (2693, 1), (2763, 1), (2794, 1), (2839, -1)]

def row450 : Integer.Sparse (Fin 3237) := [(923, 1), (927, 1), (930, 1), (936, 2), (2177, 1), (2839, -1)]

def row451 : Integer.Sparse (Fin 3237) := [(1743, 1), (2114, 1), (2116, 2), (2177, 1), (2693, 1), (2839, -1)]

def row452 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -55), (160, -80), (261, -70), (1592, -1080), (1593, -1080), (1610, -1080), (1618, -1080), (1781, -1080), (1913, -1080), (1919, -1080), (1920, -1080), (2160, -2160), (2177, -2160), (2456, -1080), (2460, -1080), (2573, -2160), (2574, -2160), (2575, -2160), (2578, -2160), (3063, 4320), (3065, 8640), (3118, 4320), (3119, 8640), (3170, 4320), (3173, 8640), (3184, 4320), (3186, 4320), (3190, 4320), (3192, 8640)]

def row453 : Integer.Sparse (Fin 3237) := [(0, -126), (32, 155), (160, 160), (162, 80), (225, 80), (261, 125), (1583, 1440), (1592, 1440), (1593, 1440), (1601, 2880), (1924, 1440), (1927, 2880), (1952, 1440), (1953, 1440), (1958, 1440), (1959, 1440), (1962, 2880), (1963, 2880)]

def row454 : Integer.Sparse (Fin 3237) := [(0, -231), (32, 235), (160, 80), (162, -320), (225, -80), (261, 310), (1913, 4320), (1919, 4320), (1920, 4320), (2128, 8640), (2134, 8640), (2135, 8640), (2160, 8640), (2164, 4320), (2165, 4320), (2168, 4320), (2176, 4320), (2177, 8640), (2178, 4320), (2240, 4320), (2241, 8640)]

def row455 : Integer.Sparse (Fin 3237) := [(1781, 1), (2456, 1), (2460, 1), (2573, 1), (2832, -1)]

def row456 : Integer.Sparse (Fin 3237) := [(0, -45), (32, -5), (160, -400), (162, -160), (225, -320), (256, -160), (261, -20), (615, 4320), (616, 4320), (620, 8640), (690, 4320), (1692, 4320), (1693, 4320), (1697, 8640), (1733, 4320), (1736, 8640), (1779, 4320), (1916, 8640), (1917, 8640), (1921, 8640), (1940, 4320), (1941, 8640), (1947, 8640), (2526, 4320), (2535, 4320), (2536, 8640)]

def row457 : Integer.Sparse (Fin 3237) := [(836, 1), (837, 1), (838, 1), (849, 2), (1959, 1), (2839, -1)]

def row458 : Integer.Sparse (Fin 3237) := [(836, 1), (1862, 2), (1953, 1), (1957, 1), (1959, 1), (2839, -1)]

def row459 : Integer.Sparse (Fin 3237) := [(941, 1), (1817, 1), (1824, 2), (1959, 1), (2145, 1), (2839, -1)]

def row460 : Integer.Sparse (Fin 3237) := [(849, 1), (1824, 1), (1873, 1), (1959, 2), (1968, 1), (2839, -1)]

def row461 : Integer.Sparse (Fin 3237) := [(0, 19), (32, 5), (160, -80), (261, 110), (1394, -4320), (1577, -4320), (1595, -2160), (1631, -2160), (1948, -4320), (1968, -2160), (2491, -4320), (2536, -2160), (2571, -2160), (2912, 8640), (2913, 8640), (2914, 8640), (2921, 17280), (3020, 8640), (3104, 8640), (3109, 17280), (3132, 17280), (3133, 17280), (3137, 17280), (3184, 8640), (3187, 8640), (3188, 8640), (3193, 17280), (3195, 17280)]

def row462 : Integer.Sparse (Fin 3237) := [(0, -376), (3, 80), (4, -60), (32, -500), (68, -320), (160, -640), (162, -320), (165, -320), (255, -320), (256, -320), (261, -480), (637, 8640), (638, 8640), (639, 8640), (658, 17280), (1744, 8640), (1745, 8640), (1757, 17280), (1824, 17280), (1825, 17280), (1841, 17280), (1954, 8640), (1955, 8640), (1959, 8640), (1964, 17280), (1968, 8640), (1970, 17280)]

def row463 : Integer.Sparse (Fin 3237) := [(0, -59), (32, -35), (160, -80), (255, -160), (256, -160), (261, -220), (1098, 4320), (1099, 4320), (1100, 8640), (1170, 4320), (1559, 4320), (1577, 8640), (1631, 4320), (1892, 4320), (1904, 8640), (1916, 8640), (1929, 8640), (1944, 8640), (1947, 4320), (1948, 8640), (1978, 8640), (2156, 4320), (2174, 4320), (2185, 8640)]

def row464 : Integer.Sparse (Fin 3237) := [(2176, 1), (2491, 2), (2536, 1), (2571, 1), (2831, -1)]

def row465 : Integer.Sparse (Fin 3237) := [(922, 1), (925, 1), (929, 1), (935, 2), (2176, 1), (2831, -1)]

def row466 : Integer.Sparse (Fin 3237) := [(922, 1), (2080, 2), (2174, 1), (2176, 2), (2831, -1)]

def row467 : Integer.Sparse (Fin 3237) := [(1378, 1), (2113, 1), (2115, 2), (2176, 1), (2831, -1)]

def row468 : Integer.Sparse (Fin 3237) := [(1394, 1), (2080, 1), (2086, 1), (2096, 1), (2176, 1), (2491, 1), (2831, -1)]

def row469 : Integer.Sparse (Fin 3237) := [(929, 1), (2086, 2), (2113, 1), (2176, 1), (2179, 1), (2831, -1)]

def row470 : Integer.Sparse (Fin 3237) := [(0, -102), (32, 95), (160, 160), (162, -240), (225, -80), (261, 185), (1917, 4320), (1919, 4320), (1949, 8640), (2127, 8640), (2132, 8640), (2134, 8640), (2158, 8640), (2163, 4320), (2164, 4320), (2167, 4320), (2168, 4320), (2173, 4320), (2176, 8640), (2177, 4320), (2187, 8640), (2211, 4320), (2212, 8640), (2214, 4320)]

def row471 : Integer.Sparse (Fin 3237) := [(820, 1), (1781, 1), (1947, 1), (1949, 2), (2832, -1)]

def row472 : Integer.Sparse (Fin 3237) := [(1491, 1), (1492, 1), (1493, 2), (1618, 1), (1947, 1), (2832, -1)]

def row473 : Integer.Sparse (Fin 3237) := [(0, 18), (32, 5), (160, -80), (256, -80), (261, -25), (866, -2160), (1837, -4320), (1933, -4320), (1936, -2160), (1979, -2160), (2315, -2160), (2490, -4320), (2502, -2160), (2519, -4320), (2538, -2160), (2727, -8640), (2750, -4320), (2769, -2160), (2968, 17280), (2969, 8640), (2970, 8640), (3128, 17280), (3131, 17280), (3133, 17280), (3147, 17280), (3149, 8640), (3151, 8640), (3194, 17280), (3195, 8640)]

def row474 : Integer.Sparse (Fin 3237) := [(0, -104), (32, -90), (160, -160), (255, -160), (261, 70), (827, 2880), (829, 1440), (831, 1440), (2032, 2880), (2051, 2880), (2052, 1440), (2054, 1440), (2084, 2880), (2086, 2880), (2186, 2880), (2187, 1440)]

def row475 : Integer.Sparse (Fin 3237) := [(0, -18), (32, -5), (160, 80), (256, 80), (261, 25), (1904, 4320), (1906, 2160), (1910, 2160), (1978, 2160), (2306, 4320), (2312, 2160), (2315, 2160), (2488, 4320), (2490, 4320), (2502, 2160), (2512, 4320), (2519, 4320), (2525, 4320), (2527, 4320), (2534, 2160), (2538, 2160), (2727, 4320), (2750, 2160)]

def row476 : Integer.Sparse (Fin 3237) := [(1969, 1), (2727, 2), (2750, 1), (2769, 1), (2840, -1)]

def row477 : Integer.Sparse (Fin 3237) := [(844, 2), (847, 1), (851, 1), (866, 1), (1969, 1), (2840, -1)]

def row478 : Integer.Sparse (Fin 3237) := [(866, 1), (1837, 2), (1969, 1), (1979, 1), (2840, -1)]

def row479 : Integer.Sparse (Fin 3237) := [(1868, 2), (1871, 1), (1874, 1), (1969, 1), (2750, 1), (2840, -1)]

def row480 : Integer.Sparse (Fin 3237) := [(844, 1), (1819, 1), (1868, 1), (1933, 1), (1967, 1), (1969, 1), (2840, -1)]

def row481 : Integer.Sparse (Fin 3237) := [(0, 113), (3, -20), (32, -10), (66, -80), (160, -320), (225, -80), (256, -240), (261, 25), (649, -4320), (651, -2160), (662, -2160), (687, -2160), (1089, -4320), (1091, -2160), (1097, -2160), (1164, -2160), (1416, -4320), (1429, -2160), (1440, -4320), (1470, -2160), (1571, -2160), (1609, -2160), (1750, -4320), (1760, -4320), (1777, -4320), (1837, -4320), (1896, -4320), (1909, -2160), (1968, -4320), (1979, -2160), (2370, -4320), (2376, -2160), (2414, -4320), (2418, -4320), (2446, -4320), (2519, -4320), (2536, -4320), (2538, -2160), (2563, -2160), (2578, -2160), (2729, -4320), (2742, -4320), (2766, -2160), (2769, -2160)]

def row482 : Integer.Sparse (Fin 3237) := [(0, -15), (3, 4), (32, 3), (66, 16), (160, 48), (256, 32), (261, 2), (649, 864), (651, 432), (662, 432), (687, 432), (1440, 864), (1470, 432), (1571, 432), (1750, 864), (1760, 864), (1777, 864), (1837, 864), (1896, 864), (1909, 432), (1968, 864), (1979, 432), (2742, 864), (2766, 432)]

def row483 : Integer.Sparse (Fin 3237) := [(0, 13), (32, -15), (160, 80), (1467, -1440), (1470, -720), (1476, -720), (1590, -1440), (1609, -720), (1617, -720), (1933, -1440), (1950, -720), (1969, -1440), (1980, -1440), (2490, -1440), (2503, -720), (2537, -1440), (2575, -720), (2579, -720), (3135, 5760), (3138, 2880), (3169, 5760), (3175, 5760), (3178, 5760), (3185, 2880), (3188, 5760), (3190, 5760), (3196, 2880), (3198, 2880)]

def row484 : Integer.Sparse (Fin 3237) := [(0, -29), (32, 35), (160, -80), (261, 20), (1590, 2160), (1609, 1080), (1617, 1080), (1923, 2160), (1931, 2160), (1933, 2160), (1939, 2160), (1955, 2160), (1958, 2160), (1965, 1080), (1969, 2160), (1971, 1080), (1974, 1080), (1975, 1080), (1980, 1080), (2182, 2160)]

def row485 : Integer.Sparse (Fin 3237) := [(0, -116), (32, 150), (160, -160), (255, -160), (261, 130), (1935, 2880), (1950, 1440), (1951, 1440), (2101, 2880), (2102, 1440), (2148, 2880), (2161, 1440), (2162, 1440), (2169, 2880), (2178, 2880), (2179, 2880)]

def row486 : Integer.Sparse (Fin 3237) := [(1467, 2), (1470, 1), (1476, 1), (2537, 1), (2832, -1)]

def row487 : Integer.Sparse (Fin 3237) := [(0, 33), (32, -5), (160, 80), (225, 80), (261, 190), (826, -4320), (1753, -4320), (1758, -4320), (1761, -4320), (1810, -4320), (1932, -4320), (1934, -8640), (1968, -4320), (2309, -4320), (2437, -4320), (2449, -4320), (2450, -4320), (2480, -4320), (2489, -4320), (2501, -8640), (2536, -4320), (2717, -4320), (2722, -4320), (2729, -4320), (2742, -4320), (2763, -4320), (2960, 17280), (2961, 17280), (2963, 17280), (2967, 17280), (3122, 17280), (3126, 17280), (3129, 17280), (3142, 17280), (3145, 17280), (3148, 17280), (3171, 17280), (3190, 17280)]

def row488 : Integer.Sparse (Fin 3237) := [(0, -67), (32, 25), (160, 80), (261, -200), (802, 1080), (804, 1080), (809, 1080), (823, 1080), (1801, 1080), (1812, 1080), (1925, 1080), (2030, 1080), (2034, 1080), (2048, 1080), (2082, 1080), (2178, 1080)]

def row489 : Integer.Sparse (Fin 3237) := [(0, -33), (32, 5), (160, -80), (225, -80), (261, -190), (2300, 4320), (2301, 4320), (2304, 4320), (2307, 4320), (2309, 4320), (2437, 4320), (2449, 4320), (2450, 4320), (2479, 4320), (2480, 4320), (2482, 4320), (2487, 4320), (2489, 4320), (2499, 4320), (2500, 4320), (2501, 8640), (2517, 4320), (2533, 4320), (2535, 4320), (2536, 4320), (2722, 4320), (2729, 4320)]

def row490 : Integer.Sparse (Fin 3237) := [(1934, 1), (2717, 1), (2742, 1), (2763, 1), (2839, -1)]

def row491 : Integer.Sparse (Fin 3237) := [(802, 1), (806, 1), (809, 1), (826, 1), (845, 1), (1934, 1), (2839, -1)]

def row492 : Integer.Sparse (Fin 3237) := [(826, 1), (1810, 1), (1934, 2), (2839, -1)]

def row493 : Integer.Sparse (Fin 3237) := [(1852, 1), (1855, 1), (1858, 1), (1869, 1), (1934, 1), (2742, 1), (2839, -1)]

def row494 : Integer.Sparse (Fin 3237) := [(1801, 1), (1810, 1), (1820, 1), (1934, 1), (2717, 1), (2839, -1)]

def row495 : Integer.Sparse (Fin 3237) := [(1753, 1), (1758, 1), (1761, 1), (1934, 1), (2839, -1)]

def row496 : Integer.Sparse (Fin 3237) := [(809, 1), (1761, 1), (1858, 1), (1934, 2), (2839, -1)]

def row497 : Integer.Sparse (Fin 3237) := [(0, 438), (4, -5), (32, 55), (71, 80), (160, 80), (256, 160), (261, 170), (600, -4320), (602, -4320), (605, -4320), (622, -4320), (654, -4320), (1064, -4320), (1065, -4320), (1066, -4320), (1069, -4320), (1156, -4320), (1681, -4320), (1683, -4320), (1684, -4320), (1698, -4320), (1727, -4320), (1728, -4320), (1737, -4320), (1753, -4320), (1755, -4320), (1810, -4320), (1815, -4320), (1932, -4320), (1933, -4320), (1934, -4320), (1936, -4320), (1948, -4320), (1950, -4320), (2342, -4320), (2343, -4320), (2344, -4320), (2346, -4320), (2405, -4320), (2406, -4320), (2408, -4320), (2437, -4320), (2438, -4320), (2480, -4320), (2481, -4320), (2489, -4320), (2490, -4320), (2491, -4320), (2501, -4320), (2502, -4320), (2503, -4320), (2557, -4320), (2570, -4320), (2575, -4320), (2783, -4320), (2786, -4320), (2803, -4320)]

def row498 : Integer.Sparse (Fin 3237) := [(0, -323), (4, 5), (32, -55), (71, -80), (160, -80), (256, -80), (261, -5), (600, 4320), (602, 4320), (605, 4320), (622, 4320), (654, 4320), (1681, 4320), (1683, 4320), (1684, 4320), (1698, 4320), (1727, 4320), (1728, 4320), (1737, 4320), (1753, 4320), (1755, 4320), (1810, 4320), (1815, 4320), (1932, 4320), (1933, 4320), (1934, 4320), (1936, 4320), (1948, 4320), (1950, 4320), (2783, 4320)]

def row499 : Integer.Sparse (Fin 3237) := [(0, 67), (32, -85), (160, -80), (261, -100), (1420, -2160), (1422, -2160), (1424, -2160), (1549, -2160), (1562, -2160), (1569, -2160), (1896, -2160), (1913, -2160), (1933, -4320), (1934, -6480), (1950, -2160), (2370, -2160), (2456, -2160), (2490, -4320), (2501, -6480), (2503, -2160), (2575, -4320), (2578, -2160), (3156, 8640), (3160, 8640), (3164, 8640), (3168, 8640), (3170, 8640), (3175, 8640), (3180, 17280), (3181, 8640)]

def row500 : Integer.Sparse (Fin 3237) := [(0, -394), (32, 500), (255, -160), (261, 510), (1549, 8640), (1562, 8640), (1569, 8640), (1889, 8640), (1896, 8640), (1897, 8640), (1902, 8640), (1913, 8640), (1915, 8640), (1924, 8640), (1933, 8640), (1934, 17280), (1935, 8640), (1941, 8640), (1942, 8640), (1950, 8640), (2147, 8640)]

def row501 : Integer.Sparse (Fin 3237) := [(0, -23), (32, 29), (160, 16), (261, 32), (1933, 216), (1934, 216), (1941, 216), (2137, 216), (2146, 216), (2147, 216), (2152, 216), (2168, 216), (2171, 216), (2182, 216), (2184, 216)]

def row502 : Integer.Sparse (Fin 3237) := [(1420, 1), (1422, 1), (1424, 1), (2501, 1), (2832, -1)]

def row503 : Integer.Sparse (Fin 3237) := [(0, 48), (32, 25), (160, 80), (256, 80), (261, -35), (822, -4320), (1752, -4320), (1755, -4320), (1760, -4320), (1808, -4320), (1933, -4320), (1936, -4320), (1948, -4320), (1969, -4320), (2303, -4320), (2429, -4320), (2438, -4320), (2446, -4320), (2475, -4320), (2490, -4320), (2491, -4320), (2502, -4320), (2537, -4320), (2716, -8640), (2727, -8640), (2764, -4320), (2959, 17280), (2961, 17280), (2962, 17280), (2968, 17280), (3123, 17280), (3128, 17280), (3131, 17280), (3141, 17280), (3144, 17280), (3147, 17280), (3175, 17280), (3194, 17280)]

def row504 : Integer.Sparse (Fin 3237) := [(0, -196), (32, -210), (160, 160), (255, 160), (261, 170), (805, 2160), (806, 2160), (808, 2160), (827, 2160), (2031, 2160), (2032, 2160), (2033, 2160), (2051, 2160), (2074, 2160), (2084, 2160), (2182, 2160), (2186, 2160)]

def row505 : Integer.Sparse (Fin 3237) := [(0, -48), (32, -25), (160, -80), (256, -80), (261, 35), (2298, 4320), (2301, 4320), (2303, 4320), (2305, 4320), (2306, 4320), (2429, 4320), (2438, 4320), (2446, 4320), (2475, 4320), (2476, 4320), (2483, 4320), (2488, 4320), (2490, 4320), (2491, 4320), (2495, 4320), (2497, 4320), (2502, 4320), (2512, 4320), (2525, 4320), (2527, 4320), (2537, 4320), (2716, 4320), (2727, 4320)]

def row506 : Integer.Sparse (Fin 3237) := [(1933, 1), (2716, 1), (2727, 1), (2764, 1), (2840, -1)]

def row507 : Integer.Sparse (Fin 3237) := [(801, 1), (804, 1), (808, 1), (822, 1), (844, 1), (1933, 1), (2840, -1)]

def row508 : Integer.Sparse (Fin 3237) := [(822, 1), (1808, 1), (1933, 1), (1948, 1), (2840, -1)]

def row509 : Integer.Sparse (Fin 3237) := [(1822, 1), (1851, 1), (1857, 1), (1868, 1), (1933, 1), (2727, 1), (2840, -1)]

def row510 : Integer.Sparse (Fin 3237) := [(801, 1), (1752, 1), (1851, 1), (1933, 2), (2840, -1)]

def row511 : Integer.Sparse (Fin 3237) := [(1803, 1), (1808, 1), (1819, 1), (1933, 1), (2716, 1), (2840, -1)]

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

def row512 : Integer.Sparse (Fin 3237) := [(0, 300), (4, -5), (32, 70), (66, 80), (160, 320), (225, 80), (256, 240), (261, 175), (598, -4320), (599, -4320), (605, -4320), (619, -4320), (653, -4320), (1047, -4320), (1048, -4320), (1054, -4320), (1066, -4320), (1142, -4320), (1359, -4320), (1367, -4320), (1373, -4320), (1376, -4320), (1391, -4320), (1421, -4320), (1551, -4320), (1561, -4320), (1680, -4320), (1684, -4320), (1696, -4320), (1728, -4320), (1735, -4320), (1752, -4320), (1808, -4320), (1815, -4320), (1913, -4320), (1920, -4320), (1932, -4320), (1933, -4320), (1934, -4320), (1948, -4320), (2331, -4320), (2335, -4320), (2344, -4320), (2402, -4320), (2406, -4320), (2429, -4320), (2456, -4320), (2460, -4320), (2475, -4320), (2481, -4320), (2489, -4320), (2490, -4320), (2491, -4320), (2501, -4320), (2554, -4320), (2570, -4320), (2717, -4320), (2722, -4320), (2723, -8640), (2763, -4320), (2764, -4320)]

def row513 : Integer.Sparse (Fin 3237) := [(0, -40), (4, 1), (32, -15), (66, -16), (160, -48), (256, -32), (261, -12), (598, 864), (599, 864), (605, 864), (619, 864), (653, 864), (1359, 864), (1373, 864), (1391, 864), (1551, 864), (1680, 864), (1684, 864), (1696, 864), (1728, 864), (1735, 864), (1752, 864), (1808, 864), (1815, 864), (1913, 864), (1920, 864), (1932, 864), (1933, 864), (1934, 864), (1948, 864), (2717, 864), (2723, 864), (2763, 864)]

def row514 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -55), (160, -80), (261, -70), (1388, -2160), (1391, -2160), (1397, -2160), (1548, -2160), (1561, -2160), (1568, -2160), (1896, -2160), (1913, -2160), (1933, -4320), (1934, -4320), (1949, -4320), (1969, -2160), (2370, -2160), (2456, -2160), (2490, -4320), (2501, -4320), (2537, -2160), (2575, -2160), (2578, -2160), (3127, 8640), (3135, 8640), (3155, 8640), (3163, 8640), (3167, 8640), (3169, 8640), (3170, 8640), (3175, 8640), (3178, 8640), (3180, 8640), (3181, 8640)]

def row515 : Integer.Sparse (Fin 3237) := [(0, -23), (32, 29), (160, 16), (261, 32), (1548, 864), (1561, 864), (1568, 864), (1888, 864), (1894, 864), (1896, 864), (1901, 864), (1913, 864), (1914, 864), (1923, 864), (1931, 864), (1933, 1728), (1934, 864), (1939, 864), (1941, 864), (1949, 864), (1969, 864), (2146, 864), (2168, 864), (2182, 864)]

def row516 : Integer.Sparse (Fin 3237) := [(0, -220), (32, 270), (160, 160), (255, 160), (261, 290), (1924, 2160), (1934, 2160), (1935, 2160), (1942, 2160), (2089, 2160), (2101, 2160), (2138, 2160), (2147, 2160), (2148, 2160), (2153, 2160), (2169, 2160), (2172, 2160)]

def row517 : Integer.Sparse (Fin 3237) := [(1388, 1), (1391, 1), (1397, 1), (2490, 1), (2832, -1)]

def row518 : Integer.Sparse (Fin 3237) := [(0, 1), (261, -1), (2319, -72), (2320, -24), (2322, -24), (2557, -144), (2564, -72), (2565, -72), (2575, -72), (2580, -24)]

def row519 : Integer.Sparse (Fin 3237) := [(0, 1), (261, 5), (2318, -90), (2320, -30), (2321, -30), (2554, -180), (2558, -90), (2563, -90), (2571, -90), (2579, -30)]

def row520 : Integer.Sparse (Fin 3237) := [(0, 1), (32, -1), (160, 16), (261, 2), (869, -144), (1470, -432), (1609, -432), (1630, -144), (1949, -864), (1969, -432), (2537, -432), (2579, -144), (2972, 1728), (2974, 576), (3135, 3456), (3138, 1728), (3195, 1728), (3200, 576)]

def row521 : Integer.Sparse (Fin 3237) := [(0, -38), (32, 40), (255, 160), (261, 30), (871, 1440), (873, 480), (1970, 1440), (1981, 480), (2101, 2880), (2102, 1440)]

def row522 : Integer.Sparse (Fin 3237) := [(0, -1), (32, 1), (160, -16), (261, -2), (1609, 432), (1630, 144), (1931, 864), (1946, 432), (1949, 432), (1965, 432), (1969, 432), (1977, 144), (1981, 144), (2187, 432)]

def row523 : Integer.Sparse (Fin 3237) := [(0, 12), (32, -5), (160, 80), (256, 80), (261, -5), (686, -2160), (689, -720), (700, -720), (1094, -2160), (1167, -720), (1776, -4320), (1789, -2160), (1908, -2160), (1979, -2160), (2538, -2160), (2579, -720)]

def row524 : Integer.Sparse (Fin 3237) := [(0, 15), (32, 5), (160, -80), (225, -80), (261, 50), (832, -2160), (1782, -4320), (1786, -2160), (1815, -4320), (1948, -4320), (1979, -2160), (2311, -2160), (2439, -4320), (2451, -2160), (2481, -4320), (2491, -4320), (2538, -2160), (2723, -8640), (2766, -2160), (2967, 17280), (2969, 8640), (2973, 8640), (3126, 17280), (3136, 17280), (3180, 17280), (3182, 8640), (3198, 8640)]

def row525 : Integer.Sparse (Fin 3237) := [(0, -47), (32, -55), (160, -80), (261, 20), (845, 1080), (847, 540), (867, 540), (1855, 1080), (1943, 540), (2098, 1080), (2147, 1080), (2161, 540)]

def row526 : Integer.Sparse (Fin 3237) := [(0, -15), (32, -5), (160, 80), (225, 80), (261, -50), (2304, 4320), (2311, 2160), (2312, 2160), (2316, 2160), (2439, 4320), (2451, 2160), (2481, 4320), (2482, 4320), (2491, 4320), (2492, 4320), (2504, 2160), (2520, 4320), (2538, 2160), (2539, 2160), (2723, 4320)]

def row527 : Integer.Sparse (Fin 3237) := [(1950, 1), (2723, 2), (2766, 1), (2840, -1)]

def row528 : Integer.Sparse (Fin 3237) := [(1812, 1), (1815, 1), (1838, 1), (1950, 1), (2723, 1), (2840, -1)]

def row529 : Integer.Sparse (Fin 3237) := [(1782, 2), (1786, 1), (1950, 1), (2840, -1)]

def row530 : Integer.Sparse (Fin 3237) := [(832, 1), (1815, 2), (1950, 1), (2840, -1)]

def row531 : Integer.Sparse (Fin 3237) := [(0, 137), (32, -25), (160, -80), (256, -160), (261, 290), (622, -4320), (625, -2160), (628, -2160), (693, -2160), (1069, -4320), (1072, -2160), (1075, -2160), (1158, -2160), (1683, -4320), (1695, -4320), (1698, -4320), (1700, -2160), (1703, -4320), (1737, -4320), (1741, -4320), (1782, -4320), (1934, -4320), (1936, -2160), (1948, -4320), (1949, -4320), (2343, -4320), (2346, -4320), (2348, -2160), (2408, -4320), (2439, -4320), (2491, -4320), (2501, -4320), (2502, -2160), (2571, -2160), (2575, -2160), (2783, -4320), (2786, -4320), (2787, -4320)]

def row532 : Integer.Sparse (Fin 3237) := [(0, -18), (32, 5), (160, 16), (256, 16), (261, -37), (622, 864), (625, 432), (628, 432), (693, 432), (1683, 864), (1698, 864), (1700, 432), (1703, 432), (1737, 864), (1741, 864), (1782, 864), (1934, 864), (1936, 432), (1948, 864), (1949, 432), (2783, 864), (2787, 432)]

def row533 : Integer.Sparse (Fin 3237) := [(0, 13), (32, -15), (160, 80), (1422, -1440), (1426, -720), (1562, -1440), (1580, -720), (1909, -720), (1920, -1440), (1934, -1440), (1950, -1440), (1969, -720), (2376, -720), (2460, -1440), (2501, -1440), (2503, -1440), (2537, -720), (2575, -720), (2579, -720), (3150, 5760), (3151, 2880), (3160, 5760), (3175, 5760), (3185, 2880), (3190, 5760), (3198, 2880)]

def row534 : Integer.Sparse (Fin 3237) := [(0, -106), (32, 120), (160, -320), (255, 160), (261, 50), (1562, 8640), (1580, 4320), (1897, 8640), (1909, 4320), (1910, 4320), (1920, 8640), (1921, 8640), (1934, 8640), (1935, 8640), (1950, 8640), (1951, 4320), (2161, 4320), (2178, 8640)]

def row535 : Integer.Sparse (Fin 3237) := [(1422, 2), (1426, 1), (2503, 1), (2832, -1)]

def row536 : Integer.Sparse (Fin 3237) := [(822, -2), (828, -1), (832, -1), (866, -1), (1755, -2), (1808, -2), (1815, -2), (1837, -2), (1933, -2), (1936, -1), (1948, -2), (1950, -1), (1969, -1), (1979, -1), (2303, -2), (2310, -1), (2311, -1), (2315, -1), (2438, -2), (2475, -2), (2481, -2), (2490, -2), (2491, -2), (2502, -1), (2503, -1), (2519, -2), (2537, -1), (2538, -1), (2840, 4)]

def row537 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -55), (160, -80), (261, -70), (1781, -4320), (1789, -2160), (1896, -4320), (1908, -2160), (1909, -2160), (1913, -4320), (1919, -4320), (1920, -4320), (1933, -4320), (1934, -4320), (1949, -4320), (1950, -2160), (2160, -2160), (2177, -4320), (2370, -4320), (2376, -2160), (2456, -4320), (2460, -4320), (2490, -4320), (2501, -4320), (2503, -2160), (2573, -4320), (2574, -2160), (2575, -2160), (2578, -2160), (2832, 8640)]

def row538 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (261, -40), (825, -2160), (1391, -4320), (1561, -4320), (1579, -2160), (1781, -4320), (1789, -2160), (1908, -2160), (1919, -4320), (1933, -4320), (1949, -8640), (1980, -4320), (2490, -4320), (2578, -2160), (2966, 17280), (2970, 8640), (2972, 8640), (3127, 17280), (3135, 17280), (3184, 17280), (3185, 8640), (3195, 8640)]

def row539 : Integer.Sparse (Fin 3237) := [(0, -106), (32, 140), (255, -160), (261, 150), (849, 2160), (851, 1080), (871, 1080), (1959, 2160), (1970, 1080), (1975, 1080), (2089, 2160), (2101, 2160)]

def row540 : Integer.Sparse (Fin 3237) := [(0, -19), (32, 25), (160, 80), (261, 40), (1561, 4320), (1579, 2160), (1894, 4320), (1906, 2160), (1908, 2160), (1917, 4320), (1919, 4320), (1931, 4320), (1933, 4320), (1946, 2160), (1949, 4320), (1980, 2160), (2158, 2160), (2176, 4320), (2187, 2160)]

def row541 : Integer.Sparse (Fin 3237) := [(0, 42), (32, 5), (160, -80), (256, -80), (261, 95), (618, -4320), (621, -2160), (628, -2160), (692, -2160), (1051, -4320), (1072, -2160), (1145, -2160), (1695, -4320), (1703, -2160), (1734, -4320), (1741, -4320), (1781, -4320), (1919, -4320), (1948, -4320), (1949, -2160), (1950, -2160), (2491, -4320), (2503, -2160), (2571, -2160)]

def row542 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (261, -40), (695, -2160), (1165, -2160), (1424, -4320), (1569, -4320), (1593, -4320), (1611, -4320), (1618, -4320), (1619, -4320), (2160, -2160), (2574, -2160), (2578, -2160), (2928, 17280), (2930, 8640), (2931, 8640), (3032, 17280), (3034, 17280), (3035, 17280), (3043, 8640), (3060, 17280), (3062, 8640), (3065, 17280), (3066, 8640), (3181, 17280), (3185, 8640)]

def row543 : Integer.Sparse (Fin 3237) := [(0, -30), (32, 35), (160, 160), (162, 80), (225, 80), (261, 5), (1150, 4320), (1165, 2160), (1166, 2160), (1172, 2160), (1554, 4320), (1569, 4320), (1570, 4320), (1574, 4320), (1575, 2160), (1593, 4320), (1601, 4320), (1602, 4320), (1611, 2160), (1619, 2160), (1621, 2160), (1625, 2160), (1942, 4320), (1975, 2160)]

def row544 : Integer.Sparse (Fin 3237) := [(695, 1), (1424, 2), (1611, 1), (1620, 1), (2832, -1)]

def row545 : Integer.Sparse (Fin 3237) := [(0, 27), (32, 5), (160, -80), (225, 160), (261, 230), (502, -4320), (503, -2160), (505, -2160), (518, -2160), (1315, -4320), (1316, -4320), (1318, -4320), (1329, -4320), (1471, -4320), (1473, -2160), (1476, -2160), (1616, -4320), (1617, -2160), (1620, -4320), (1622, -2160), (1628, -2160), (1632, -2160), (2704, -4320), (2766, -2160)]

def row546 : Integer.Sparse (Fin 3237) := [(0, 17), (32, -20), (160, 80), (261, -5), (693, -1080), (1158, -1080), (1422, -2160), (1562, -2160), (1593, -2160), (1611, -2160), (1618, -2160), (1619, -2160), (1620, -2160), (1622, -1080), (1632, -1080), (2578, -1080), (2579, -1080), (2927, 8640), (2929, 4320), (2931, 4320), (3031, 8640), (3033, 8640), (3035, 8640), (3059, 8640), (3061, 4320), (3062, 4320), (3175, 8640), (3195, 4320)]

def row547 : Integer.Sparse (Fin 3237) := [(0, -57), (32, 50), (160, -80), (162, -80), (261, 35), (914, 1440), (916, 720), (919, 720), (1769, 1440), (1787, 720), (2182, 1440), (2187, 720), (2214, 1440), (2217, 720), (2235, 1440), (2236, 1440)]

def row548 : Integer.Sparse (Fin 3237) := [(0, -17), (32, 20), (160, -80), (261, 5), (1144, 2160), (1158, 1080), (1159, 1080), (1166, 1080), (1550, 2160), (1562, 2160), (1563, 2160), (1570, 2160), (1593, 2160), (1594, 2160), (1611, 2160), (1612, 1080), (1620, 1080), (1621, 1080), (1632, 1080), (1935, 2160), (1970, 1080)]

def row549 : Integer.Sparse (Fin 3237) := [(670, 2), (672, 1), (676, 1), (693, 1), (1619, 1), (2832, -1)]

def row550 : Integer.Sparse (Fin 3237) := [(693, 1), (1422, 2), (1619, 1), (2832, -1)]

def row551 : Integer.Sparse (Fin 3237) := [(0, 73), (32, 10), (160, -160), (225, -240), (256, -80), (261, 145), (490, -4320), (491, -2160), (493, -2160), (499, -4320), (501, -2160), (506, -2160), (517, -2160), (519, -2160), (1305, -4320), (1306, -4320), (1308, -4320), (1312, -4320), (1314, -4320), (1319, -4320), (1328, -4320), (1330, -4320), (1424, -4320), (1426, -2160), (1429, -2160), (1468, -4320), (1470, -2160), (1477, -2160), (1569, -4320), (1571, -2160), (1580, -2160), (1593, -4320), (1595, -2160), (1608, -4320), (1609, -2160), (1611, -2160), (1618, -4320), (1619, -2160), (1629, -2160), (1631, -2160), (2699, -4320), (2703, -4320), (2766, -2160), (2769, -2160)]

def row552 : Integer.Sparse (Fin 3237) := [(0, -38), (32, -5), (160, 80), (225, 80), (256, 80), (261, -35), (499, 4320), (501, 2160), (506, 2160), (517, 2160), (1312, 4320), (1314, 4320), (1319, 4320), (1328, 4320), (1468, 4320), (1470, 2160), (1477, 2160), (1569, 4320), (1571, 2160), (1580, 2160), (1618, 4320), (1619, 2160), (1631, 2160), (2703, 4320), (2766, 2160)]

def row553 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (662, -360), (695, -360), (1164, -360), (1165, -360), (1397, -720), (1424, -720), (1476, -360), (1568, -720), (1569, -720), (1592, -720), (1610, -720), (1617, -360), (1620, -720), (2160, -360), (2574, -360), (2575, -360), (2920, 2880), (2922, 1440), (3026, 2880), (3028, 2880), (3055, 2880), (3057, 1440), (3065, 2880), (3066, 1440), (3180, 2880), (3198, 1440)]

def row554 : Integer.Sparse (Fin 3237) := [(0, -35), (32, 40), (160, 80), (162, 80), (225, 80), (261, -5), (1149, 4320), (1164, 2160), (1165, 2160), (1171, 2160), (1553, 4320), (1568, 4320), (1569, 4320), (1573, 4320), (1592, 4320), (1599, 4320), (1601, 4320), (1617, 2160), (1620, 2160), (1623, 2160), (1625, 2160), (1941, 4320), (1974, 2160)]

def row555 : Integer.Sparse (Fin 3237) := [(0, -57), (32, 50), (160, -80), (162, -80), (261, 35), (936, 1440), (938, 720), (1453, 1440), (1474, 720), (1603, 720), (2147, 1440), (2160, 720), (2161, 720), (2230, 1440), (2238, 1440), (2241, 1440)]

def row556 : Integer.Sparse (Fin 3237) := [(655, 2), (660, 1), (662, 1), (695, 1), (1611, 1), (2832, -1)]

def row557 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (657, -8640), (1163, -8640), (1392, -8640), (1471, -8640), (1567, -8640), (1591, -8640), (1592, -4320), (1593, -8640), (1610, -4320), (1616, -8640), (1618, -8640), (2159, -4320), (2567, -4320), (2570, -4320), (2910, 17280), (2913, 17280), (2915, 17280), (3021, 17280), (3023, 17280), (3028, 34560), (3048, 34560), (3052, 34560), (3063, 17280), (3064, 17280), (3179, 17280), (3197, 34560)]

def row558 : Integer.Sparse (Fin 3237) := [(0, -29), (32, -35), (160, -160), (162, -80), (225, -120), (261, -50), (1148, 2160), (1162, 2160), (1163, 4320), (1170, 2160), (1566, 2160), (1567, 4320), (1572, 2160), (1573, 4320), (1591, 2160), (1598, 4320), (1600, 2160), (1610, 2160), (1615, 4320), (1616, 4320), (1618, 4320), (1624, 2160), (1940, 2160), (1973, 4320)]

def row559 : Integer.Sparse (Fin 3237) := [(1593, 1), (2484, 1), (2528, 2), (2567, 1), (2570, 1), (2831, -1)]

def row560 : Integer.Sparse (Fin 3237) := [(657, 1), (1392, 1), (1471, 1), (1593, 2), (2831, -1)]

def row561 : Integer.Sparse (Fin 3237) := [(1450, 1), (1453, 1), (1455, 1), (1471, 1), (1593, 1), (2528, 1), (2831, -1)]

def row562 : Integer.Sparse (Fin 3237) := [(1379, 1), (1381, 1), (1392, 2), (1593, 1), (2484, 1), (2831, -1)]

def row563 : Integer.Sparse (Fin 3237) := [(640, 1), (1381, 1), (1455, 2), (1592, 1), (1593, 1), (2831, -1)]

def row564 : Integer.Sparse (Fin 3237) := [(0, 93), (32, 15), (160, 240), (225, 40), (256, 80), (261, -90), (472, -2160), (473, -2160), (474, -2160), (490, -4320), (497, -2160), (498, -2160), (499, -4320), (514, -2160), (1294, -2160), (1295, -2160), (1305, -4320), (1311, -2160), (1312, -4320), (1325, -2160), (1392, -4320), (1394, -4320), (1397, -4320), (1424, -4320), (1466, -2160), (1467, -2160), (1468, -4320), (1567, -4320), (1568, -4320), (1569, -4320), (1577, -4320), (1589, -2160), (1590, -2160), (1593, -2160), (1595, -2160), (1608, -4320), (1611, -4320), (1618, -2160), (1619, -4320), (1631, -2160), (2694, -2160), (2702, -2160), (2765, -4320), (2768, -2160)]

def row565 : Integer.Sparse (Fin 3237) := [(0, -28), (32, -10), (160, -80), (225, -40), (261, 50), (472, 1080), (473, 1080), (474, 1080), (490, 2160), (1294, 1080), (1295, 1080), (1305, 2160), (1392, 2160), (1394, 2160), (1397, 2160), (1424, 2160), (1589, 1080), (1590, 1080), (1593, 1080), (1595, 1080), (1608, 2160), (1611, 2160), (2694, 1080), (2768, 1080)]

def row566 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (261, -40), (691, -1080), (1143, -1080), (1420, -1080), (1549, -1080), (1592, -1080), (1593, -2160), (1610, -1080), (1611, -2160), (1618, -2160), (1619, -2160), (1620, -4320), (2177, -1080), (2573, -1080), (2578, -2160), (2926, 4320), (2927, 4320), (2928, 8640), (3031, 4320), (3032, 8640), (3058, 4320), (3059, 4320), (3060, 8640), (3063, 4320), (3065, 8640), (3170, 4320), (3184, 4320)]

def row567 : Integer.Sparse (Fin 3237) := [(0, -94), (32, 125), (160, 160), (162, -80), (225, -80), (261, 215), (1137, 4320), (1143, 4320), (1144, 4320), (1150, 8640), (1549, 4320), (1550, 4320), (1554, 8640), (1583, 4320), (1584, 4320), (1592, 4320), (1593, 8640), (1594, 4320), (1601, 8640), (1602, 8640), (1611, 8640), (1620, 8640), (1924, 4320), (1959, 4320)]

def row568 : Integer.Sparse (Fin 3237) := [(0, -118), (32, 185), (160, 160), (162, 240), (225, 80), (261, 155), (910, 1440), (911, 2880), (914, 1440), (2168, 1440), (2176, 1440), (2177, 1440), (2211, 1440), (2212, 2880), (2214, 1440), (2234, 2880), (2235, 1440), (2240, 1440), (2241, 2880)]

def row569 : Integer.Sparse (Fin 3237) := [(669, 1), (670, 1), (671, 2), (691, 1), (1618, 1), (2832, -1)]

def row570 : Integer.Sparse (Fin 3237) := [(0, 17), (32, 13), (160, -16), (261, 40), (654, -1728), (1156, -1728), (1389, -1728), (1468, -1728), (1560, -1728), (1591, -1728), (1592, -864), (1593, -864), (1595, -864), (1608, -1728), (1610, -864), (1618, -864), (1631, -864), (2570, -864), (2571, -864), (2911, 3456), (2915, 3456), (3020, 3456), (3023, 3456), (3047, 6912), (3049, 6912), (3052, 6912), (3194, 6912)]

def row571 : Integer.Sparse (Fin 3237) := [(0, -99), (32, -140), (160, 80), (162, 80), (261, -185), (927, 1080), (930, 1080), (1744, 1080), (1759, 2160), (2186, 2160), (2225, 2160), (2226, 2160), (2237, 1080)]

def row572 : Integer.Sparse (Fin 3237) := [(0, -17), (32, -13), (160, 16), (261, -40), (1155, 864), (1156, 1728), (1162, 864), (1559, 864), (1560, 1728), (1566, 864), (1588, 1728), (1591, 864), (1607, 1728), (1608, 1728), (1610, 864), (1615, 1728), (1618, 864), (1631, 864), (1967, 1728)]

def row573 : Integer.Sparse (Fin 3237) := [(1592, 1), (2527, 2), (2570, 1), (2571, 1), (2831, -1)]

def row574 : Integer.Sparse (Fin 3237) := [(636, 1), (640, 1), (654, 2), (1592, 1), (2831, -1)]

def row575 : Integer.Sparse (Fin 3237) := [(654, 1), (1389, 1), (1468, 1), (1592, 1), (2831, -1)]

def row576 : Integer.Sparse (Fin 3237) := [(1449, 1), (1451, 1), (1455, 1), (1468, 1), (1592, 1), (2527, 1), (2831, -1)]

def row577 : Integer.Sparse (Fin 3237) := [(1449, 2), (1591, 1), (1592, 2), (2831, -1)]

def row578 : Integer.Sparse (Fin 3237) := [(0, 269), (32, 45), (160, 240), (225, 240), (256, 160), (261, -180), (469, -4320), (471, -4320), (475, -4320), (486, -4320), (487, -4320), (488, -17280), (515, -4320), (1293, -4320), (1296, -4320), (1302, -4320), (1303, -17280), (1326, -4320), (1389, -8640), (1391, -8640), (1398, -8640), (1420, -4320), (1421, -4320), (1422, -17280), (1549, -4320), (1551, -4320), (1560, -8640), (1561, -8640), (1562, -17280), (1578, -8640), (1591, -8640), (1592, -12960), (1610, -12960), (2693, -4320), (2698, -4320), (2763, -4320), (2764, -8640)]

def row579 : Integer.Sparse (Fin 3237) := [(0, -83), (32, -25), (160, -80), (225, -40), (256, -80), (261, 110), (469, 2160), (471, 2160), (475, 2160), (488, 4320), (1293, 2160), (1296, 2160), (1303, 4320), (1389, 4320), (1391, 4320), (1398, 4320), (1422, 4320), (1549, 2160), (1551, 2160), (1562, 4320), (1591, 2160), (1592, 2160), (1610, 4320), (2693, 2160), (2763, 2160)]

def row580 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (653, -180), (691, -180), (1142, -180), (1143, -180), (1388, -180), (1420, -180), (1467, -180), (1548, -180), (1549, -180), (1590, -180), (1592, -360), (1593, -180), (1610, -360), (1611, -360), (1618, -180), (1619, -360), (2177, -180), (2573, -180), (2575, -360), (2920, 1440), (3026, 1440), (3054, 720), (3055, 1440), (3063, 720), (3065, 1440), (3190, 720)]

def row581 : Integer.Sparse (Fin 3237) := [(0, -114), (32, 145), (160, -160), (162, -80), (225, -80), (261, 175), (1142, 4320), (1143, 4320), (1149, 8640), (1548, 4320), (1549, 4320), (1553, 8640), (1582, 4320), (1583, 4320), (1590, 4320), (1592, 8640), (1593, 4320), (1599, 8640), (1601, 8640), (1619, 8640), (1958, 4320)]

def row582 : Integer.Sparse (Fin 3237) := [(0, -111), (32, 160), (160, 80), (162, 80), (261, 175), (936, 2160), (2177, 1080), (2178, 1080), (2229, 1080), (2230, 2160), (2238, 2160), (2240, 1080), (2241, 2160)]

def row583 : Integer.Sparse (Fin 3237) := [(653, 1), (655, 2), (691, 1), (1610, 1), (2832, -1)]

def row584 : Integer.Sparse (Fin 3237) := [(0, 19), (32, 5), (160, -80), (261, 110), (654, -4320), (659, -2160), (663, -2160), (1156, -4320), (1176, -2160), (1177, -2160), (1389, -4320), (1394, -4320), (1398, -4320), (1468, -4320), (1473, -2160), (1477, -2160), (1560, -4320), (1577, -4320), (1578, -4320), (1592, -4320), (1595, -2160), (1608, -4320), (1610, -4320), (1628, -2160), (1629, -2160), (1631, -2160), (1948, -4320), (1979, -2160), (2491, -4320), (2538, -2160), (2571, -2160), (2831, 8640)]

def row585 : Integer.Sparse (Fin 3237) := [(0, -19), (32, -5), (160, 80), (261, -110), (1156, 4320), (1176, 2160), (1177, 2160), (1560, 4320), (1577, 4320), (1578, 4320), (1608, 4320), (1610, 4320), (1628, 2160), (1629, 2160), (1631, 2160), (1948, 4320), (1979, 2160), (2831, 2160)]

def row586 : Integer.Sparse (Fin 3237) := [(1468, 2), (1473, 1), (1477, 1), (2538, 1), (2831, -1)]

def row587 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -55), (160, -80), (261, -70), (691, -4320), (693, -2160), (695, -2160), (1143, -4320), (1158, -2160), (1165, -2160), (1420, -4320), (1422, -4320), (1424, -4320), (1549, -4320), (1562, -4320), (1569, -4320), (1592, -4320), (1593, -4320), (1610, -4320), (1611, -4320), (1618, -4320), (1619, -4320), (1620, -4320), (1934, -4320), (2501, -4320), (2575, -2160), (2578, -2160), (2832, 8640)]

def row588 : Integer.Sparse (Fin 3237) := [(0, 4), (32, -5), (261, -5), (653, -720), (656, -360), (662, -360), (1142, -720), (1157, -360), (1164, -360), (1388, -720), (1391, -720), (1397, -720), (1467, -720), (1470, -360), (1476, -360), (1548, -720), (1561, -720), (1568, -720), (1590, -720), (1592, -720), (1609, -360), (1610, -720), (1611, -360), (1617, -360), (1619, -360), (1933, -720), (1969, -360), (2490, -720), (2537, -360), (2575, -360), (2832, 1440)]

def row589 : Integer.Sparse (Fin 3237) := [(0, 1), (32, -1), (160, 16), (261, 2), (693, -432), (697, -144), (1158, -432), (1179, -144), (1422, -864), (1426, -432), (1562, -864), (1580, -432), (1611, -432), (1619, -432), (1622, -144), (1632, -144), (1950, -432), (2503, -432), (2579, -144), (2832, 576)]

def row590 : Integer.Sparse (Fin 3237) := [(0, -3), (261, -5), (2817, 120), (2818, 40), (2819, 40), (2828, 240), (2829, 120), (2830, 120), (2831, 120), (2832, 160), (2833, 40), (2840, 120)]

def row591 : Integer.Sparse (Fin 3237) := [(0, -604), (3, -160), (4, 20), (32, -30), (66, 320), (68, 320), (160, 640), (162, 160), (165, 320), (225, 320), (261, 290), (799, 17280), (805, 8640), (815, 8640), (843, 8640), (2028, 17280), (2031, 8640), (2040, 8640), (2116, 17280), (2128, 17280), (2133, 8640), (2145, 8640), (2182, 17280), (2186, 17280), (2694, 8640), (2780, 8640)]

def row592 : Integer.Sparse (Fin 3237) := [(0, -104), (32, -15), (160, 480), (162, 240), (225, 320), (261, -75), (2295, 8640), (2296, 4320), (2298, 4320), (2299, 4320), (2429, 4320), (2430, 4320), (2433, 8640), (2483, 4320), (2484, 4320), (2485, 8640), (2486, 8640), (2490, 8640), (2491, 8640), (2497, 8640), (2521, 4320), (2522, 4320), (2527, 8640), (2693, 4320), (2724, 4320)]

def row593 : Integer.Sparse (Fin 3237) := [(2698, 1), (2702, 1), (2740, 1), (2764, 2), (2840, -1)]

def row594 : Integer.Sparse (Fin 3237) := [(801, 1), (803, 2), (819, 1), (842, 1), (2840, -1)]

def row595 : Integer.Sparse (Fin 3237) := [(842, 1), (1866, 1), (1961, 1), (1967, 2), (2840, -1)]

def row596 : Integer.Sparse (Fin 3237) := [(1752, 1), (1754, 2), (1780, 1), (2698, 1), (2840, -1)]

def row597 : Integer.Sparse (Fin 3237) := [(819, 1), (1780, 1), (1940, 1), (1948, 2), (2840, -1)]

def row598 : Integer.Sparse (Fin 3237) := [(1851, 1), (1853, 2), (1866, 1), (2740, 1), (2840, -1)]

def row599 : Integer.Sparse (Fin 3237) := [(0, 17), (32, 13), (160, -16), (261, 40), (1389, -1728), (1560, -1728), (1592, -864), (1610, -864), (1932, -2592), (1948, -1728), (1968, -864), (2489, -2592), (2491, -1728), (2536, -864), (2570, -864), (2571, -864), (3020, 3456), (3023, 3456), (3104, 3456), (3109, 6912), (3159, 6912), (3161, 3456), (3174, 13824), (3176, 6912), (3177, 3456), (3179, 3456), (3184, 3456), (3194, 6912)]

def row600 : Integer.Sparse (Fin 3237) := [(0, -41), (32, -25), (160, 80), (261, -140), (1559, 1440), (1560, 2880), (1566, 1440), (1610, 1440), (1892, 1440), (1893, 2880), (1899, 1440), (1929, 2880), (1930, 2880), (1932, 2880), (1937, 2880), (1940, 1440), (1947, 1440), (1948, 2880), (1967, 2880), (2144, 1440), (2181, 2880)]

def row601 : Integer.Sparse (Fin 3237) := [(0, -588), (3, -400), (4, 60), (32, -330), (68, 320), (71, 320), (160, 1920), (162, 480), (165, 320), (251, -960), (255, 640), (256, 640), (261, -1570), (1744, 8640), (1745, 8640), (1757, 17280), (1930, 17280), (1932, 8640), (1938, 8640), (1959, 8640), (1968, 8640), (2142, 17280), (2145, 8640), (2149, 8640), (2181, 17280), (2183, 17280), (2186, 17280), (2237, 8640)]

def row602 : Integer.Sparse (Fin 3237) := [(2465, 2), (2467, 1), (2489, 1), (2536, 1), (2831, -1)]

def row603 : Integer.Sparse (Fin 3237) := [(2113, 1), (2353, 1), (2356, 2), (2467, 1), (2831, -1)]

def row604 : Integer.Sparse (Fin 3237) := [(1381, 1), (2353, 1), (2462, 2), (2484, 1), (2831, -1)]

def row605 : Integer.Sparse (Fin 3237) := [(1389, 1), (2356, 1), (2465, 1), (2489, 1), (2491, 1), (2831, -1)]

def row606 : Integer.Sparse (Fin 3237) := [(2115, 1), (2462, 1), (2465, 2), (2527, 1), (2831, -1)]

def row607 : Integer.Sparse (Fin 3237) := [(0, -185), (3, 20), (4, -10), (32, -5), (68, 80), (160, 320), (162, 240), (165, 160), (256, 160), (261, 270), (768, 8640), (770, 4320), (773, 4320), (843, 4320), (2011, 8640), (2012, 4320), (2014, 4320), (2107, 8640), (2109, 4320), (2128, 8640), (2133, 4320), (2146, 8640), (2147, 8640), (2157, 8640), (2484, 4320), (2694, 4320)]

def row608 : Integer.Sparse (Fin 3237) := [(0, -16), (32, -1), (160, 64), (162, 48), (256, 32), (261, 35), (2011, 1728), (2012, 864), (2014, 864), (2145, 864), (2248, 1728), (2249, 864), (2251, 864), (2299, 864), (2430, 864), (2431, 864), (2434, 1728), (2486, 1728), (2491, 1728), (2492, 1728), (2498, 1728), (2522, 864), (2528, 1728), (2694, 864)]

def row609 : Integer.Sparse (Fin 3237) := [(1940, 2), (2702, 2), (2765, 2), (2840, -1)]

def row610 : Integer.Sparse (Fin 3237) := [(852, 1), (1875, 1), (1940, 1), (1961, 1), (1973, 2), (2840, -1)]

def row611 : Integer.Sparse (Fin 3237) := [(1765, 1), (1766, 2), (1780, 1), (1940, 1), (2702, 1), (2840, -1)]

def row612 : Integer.Sparse (Fin 3237) := [(0, 17), (32, -5), (160, 80), (225, 40), (256, 80), (261, -50), (2046, -2160), (2159, -2160), (2566, -2160), (2567, -2160), (2726, -4320), (2741, -4320), (2768, -2160), (2782, -4320), (2899, 8640), (2900, 17280), (2903, 8640), (2926, 8640), (3092, 8640), (3093, 17280), (3094, 8640), (3132, 17280), (3141, 8640), (3142, 17280), (3167, 17280), (3168, 17280), (3179, 17280), (3180, 17280), (3184, 8640), (3228, 8640)]

def row613 : Integer.Sparse (Fin 3237) := [(0, -70), (3, 60), (4, -15), (32, 225), (159, -720), (160, 640), (165, 240), (256, 400), (261, -370), (274, -480), (607, 4320), (608, 8640), (615, 4320), (669, 4320), (1685, 4320), (1686, 8640), (1692, 4320), (1851, 4320), (1852, 8640), (1914, 8640), (1915, 8640), (1916, 8640), (1940, 8640), (1941, 8640), (1947, 4320), (2740, 4320), (2741, 8640)]

def row614 : Integer.Sparse (Fin 3237) := [(0, -16), (32, 50), (160, 640), (225, 280), (252, -240), (255, 160), (256, 400), (261, -230), (1045, 2160), (1046, 2160), (1050, 4320), (1137, 2160), (2072, 2160), (2080, 4320), (2176, 2160), (2330, 2160), (2333, 4320), (2453, 4320), (2459, 4320), (2483, 2160), (2484, 4320), (2487, 4320), (2492, 4320), (2566, 2160), (2567, 2160), (2780, 2160), (2782, 2160)]

def row615 : Integer.Sparse (Fin 3237) := [(2145, 1), (2724, 1), (2726, 2), (2768, 1), (2782, 1), (2839, -1)]

def row616 : Integer.Sparse (Fin 3237) := [(903, 2), (905, 1), (910, 1), (941, 1), (2145, 1), (2839, -1)]

def row617 : Integer.Sparse (Fin 3237) := [(910, 1), (2046, 1), (2145, 3), (2159, 1), (2839, -1)]

def row618 : Integer.Sparse (Fin 3237) := [(2030, 2), (2031, 1), (2046, 1), (2145, 1), (2782, 1), (2839, -1)]

def row619 : Integer.Sparse (Fin 3237) := [(1824, 1), (2137, 1), (2138, 1), (2145, 2), (2726, 1), (2839, -1)]

def row620 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1392, -8640), (1567, -8640), (1593, -4320), (1618, -4320), (1895, -4320), (1932, -12960), (2159, -4320), (2369, -4320), (2489, -12960), (2567, -4320), (2570, -4320), (3021, 17280), (3022, 17280), (3023, 17280), (3027, 34560), (3058, 17280), (3159, 34560), (3161, 17280), (3162, 51840), (3176, 34560), (3177, 34560), (3179, 34560), (3197, 34560)]

def row621 : Integer.Sparse (Fin 3237) := [(0, -109), (3, 60), (32, -160), (68, 240), (160, 1040), (224, -720), (255, 640), (256, 640), (260, -180), (261, -395), (1478, 4320), (1479, 8640), (1491, 4320), (1566, 4320), (1567, 8640), (1572, 4320), (1618, 4320), (1899, 4320), (1900, 8640), (1932, 8640), (1937, 8640), (1938, 8640), (1940, 8640), (1973, 8640), (2151, 4320), (2183, 8640)]

def row622 : Integer.Sparse (Fin 3237) := [(0, -169), (3, -120), (4, 20), (32, -50), (66, 160), (68, 480), (160, 1840), (162, 1200), (165, 320), (219, -480), (225, 560), (255, 320), (256, 320), (261, -525), (1379, 4320), (1380, 4320), (1393, 8640), (1584, 4320), (1893, 8640), (1895, 4320), (1900, 4320), (1932, 4320), (2142, 8640), (2144, 8640), (2145, 8640), (2149, 4320), (2151, 8640), (2157, 8640), (2159, 4320), (2237, 4320)]

def row623 : Integer.Sparse (Fin 3237) := [(2356, 2), (2358, 1), (2369, 1), (2484, 1), (2489, 1), (2831, -1)]

def row624 : Integer.Sparse (Fin 3237) := [(2206, 1), (2353, 1), (2358, 3), (2484, 1), (2831, -1)]

def row625 : Integer.Sparse (Fin 3237) := [(1379, 1), (2205, 2), (2206, 1), (2211, 1), (2484, 1), (2831, -1)]

def row626 : Integer.Sparse (Fin 3237) := [(1392, 1), (2358, 1), (2467, 1), (2484, 2), (2489, 1), (2831, -1)]

def row627 : Integer.Sparse (Fin 3237) := [(2205, 1), (2356, 1), (2462, 1), (2467, 1), (2484, 1), (2528, 1), (2831, -1)]

def row628 : Integer.Sparse (Fin 3237) := [(0, 116), (32, -10), (160, 160), (225, -40), (261, 530), (865, -2160), (866, -2160), (2097, -4320), (2159, -2160), (2160, -2160), (2314, -2160), (2315, -2160), (2318, -1080), (2554, -2160), (2556, -4320), (2567, -2160), (2571, -4320), (2574, -2160), (2579, -2160), (2763, -2160)]

def row629 : Integer.Sparse (Fin 3237) := [(0, -53), (32, 5), (160, -80), (261, -250), (865, 1080), (866, 1080), (2097, 2160), (2159, 1080), (2160, 1080)]

def row630 : Integer.Sparse (Fin 3237) := [(0, 118), (32, -5), (160, 80), (256, -80), (261, -95), (691, -2160), (692, -1080), (693, -2160), (1143, -2160), (1145, -1080), (1158, -2160), (1780, -2160), (1781, -2160), (1782, -4320), (1919, -2160), (1948, -4320), (1949, -4320), (1950, -2160), (2430, -2160), (2439, -4320), (2491, -4320), (2503, -2160), (2570, -2160), (2575, -2160), (2794, -2160)]

def row631 : Integer.Sparse (Fin 3237) := [(0, -19), (32, 1), (160, -16), (261, 16), (691, 432), (692, 216), (693, 432), (1780, 432), (1781, 432), (1782, 864), (1948, 864), (1949, 432), (1950, 432)]

def row632 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1592, -4320), (1595, -2160), (1610, -4320), (1631, -2160), (1948, -8640), (1968, -4320), (1979, -8640), (2491, -8640), (2536, -4320), (2538, -8640), (2570, -4320), (3184, 17280), (3194, 34560), (3195, 17280)]

def row633 : Integer.Sparse (Fin 3237) := [(0, -47), (32, -55), (160, -80), (261, 20), (1959, 1080), (1968, 1080), (1970, 1080), (1979, 1080), (2186, 2160)]

def row634 : Integer.Sparse (Fin 3237) := [(2536, 2), (2538, 2), (2571, 1), (2831, -1)]

def row635 : Integer.Sparse (Fin 3237) := [(0, -206), (32, -30), (160, 160), (255, 160), (256, 160), (261, 200), (815, 4320), (816, 4320), (817, 4320), (827, 4320), (863, 4320), (2040, 4320), (2041, 4320), (2042, 4320), (2051, 4320), (2078, 4320), (2079, 4320), (2084, 4320), (2095, 4320), (2133, 4320), (2134, 4320), (2135, 4320), (2157, 4320), (2182, 4320), (2186, 4320), (2187, 4320), (2699, 4320), (2784, 4320), (2789, 4320)]

def row636 : Integer.Sparse (Fin 3237) := [(0, -106), (32, -65), (160, -160), (162, -80), (225, -160), (261, 205), (1772, 4320), (1774, 4320), (1778, 4320), (1783, 4320), (1978, 4320), (2296, 4320), (2297, 4320), (2306, 4320), (2313, 4320), (2490, 4320), (2491, 4320), (2497, 4320), (2512, 4320), (2513, 4320), (2515, 4320), (2521, 4320), (2522, 4320), (2525, 4320), (2527, 4320), (2528, 4320), (2530, 4320), (2532, 4320), (2537, 4320), (2538, 4320), (2737, 4320), (2747, 4320)]

def row637 : Integer.Sparse (Fin 3237) := [(1967, 1), (2703, 1), (2725, 1), (2748, 1), (2764, 1), (2769, 1), (2840, -1)]

def row638 : Integer.Sparse (Fin 3237) := [(842, 1), (844, 1), (846, 1), (848, 1), (863, 1), (1967, 1), (2840, -1)]

def row639 : Integer.Sparse (Fin 3237) := [(1819, 1), (1821, 1), (1823, 1), (1834, 1), (1967, 1), (2725, 1), (2840, -1)]

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

def row640 : Integer.Sparse (Fin 3237) := [(863, 1), (1834, 1), (1948, 1), (1967, 1), (1973, 1), (1979, 1), (2840, -1)]

def row641 : Integer.Sparse (Fin 3237) := [(1866, 1), (1868, 1), (1870, 1), (1872, 1), (1967, 1), (2748, 1), (2840, -1)]

def row642 : Integer.Sparse (Fin 3237) := [(0, 49), (32, -5), (160, 80), (256, 160), (261, -50), (2097, -4320), (2177, -4320), (2556, -4320), (2573, -4320), (2729, -4320), (2742, -4320), (2793, -17280), (2794, -4320), (2917, 17280), (2918, 17280), (2919, 17280), (2920, 17280), (2934, 17280), (3106, 17280), (3107, 17280), (3108, 17280), (3117, 17280), (3127, 17280), (3134, 17280), (3135, 34560), (3136, 17280), (3159, 17280), (3160, 17280), (3166, 17280), (3174, 17280), (3175, 17280), (3183, 17280), (3189, 17280), (3190, 17280), (3194, 17280), (3236, 17280)]

def row643 : Integer.Sparse (Fin 3237) := [(0, -98), (3, -20), (4, 5), (32, 45), (66, -80), (68, -80), (160, -400), (162, -160), (225, -160), (255, -80), (256, -160), (261, -30), (646, 4320), (647, 4320), (650, 4320), (655, 4320), (683, 4320), (1749, 4320), (1751, 4320), (1754, 4320), (1773, 4320), (1834, 4320), (1835, 4320), (1838, 4320), (1893, 4320), (1894, 4320), (1897, 4320), (1905, 4320), (1930, 4320), (1931, 4320), (1935, 4320), (1945, 4320), (1957, 4320), (1958, 4320), (1967, 4320), (2729, 4320), (2792, 4320), (2793, 4320)]

def row644 : Integer.Sparse (Fin 3237) := [(0, -84), (32, 20), (160, -480), (225, -80), (255, -160), (256, -320), (261, 120), (1080, 4320), (1081, 4320), (1085, 4320), (1090, 4320), (1149, 4320), (1806, 4320), (1814, 4320), (1835, 4320), (1931, 4320), (2356, 4320), (2360, 4320), (2371, 4320), (2412, 4320), (2415, 4320), (2433, 4320), (2465, 4320), (2469, 4320), (2497, 4320), (2513, 4320), (2520, 4320), (2526, 4320), (2527, 4320), (2535, 4320), (2556, 4320), (2573, 4320), (2792, 4320), (2793, 4320)]

def row645 : Integer.Sparse (Fin 3237) := [(2186, 1), (2742, 1), (2792, 1), (2793, 2), (2794, 1), (2839, -1)]

def row646 : Integer.Sparse (Fin 3237) := [(934, 1), (2095, 1), (2175, 1), (2181, 1), (2183, 1), (2186, 1), (2839, -1)]

def row647 : Integer.Sparse (Fin 3237) := [(2095, 1), (2097, 1), (2098, 1), (2101, 1), (2186, 1), (2793, 1), (2839, -1)]

def row648 : Integer.Sparse (Fin 3237) := [(2089, 1), (2183, 1), (2184, 1), (2186, 1), (2189, 1), (2742, 1), (2839, -1)]

def row649 : Integer.Sparse (Fin 3237) := [(0, -290), (32, -270), (160, 160), (255, 160), (256, 160), (261, -340), (1588, 8640), (1607, 8640), (1608, 8640), (1610, 8640), (1615, 8640), (1831, 8640), (1832, 8640), (1833, 8640), (1841, 8640), (1929, 8640), (1930, 8640), (1937, 8640), (1956, 8640), (1957, 8640), (1964, 8640), (1966, 8640), (1967, 17280), (1968, 8640), (1972, 8640), (1973, 8640), (1978, 8640), (1979, 8640), (2181, 8640), (2188, 8640)]

def row650 : Integer.Sparse (Fin 3237) := [(2096, 1), (2465, 1), (2469, 1), (2491, 1), (2527, 1), (2538, 1), (2831, -1)]

def row651 : Integer.Sparse (Fin 3237) := [(1449, 1), (2094, 1), (2505, 1), (2526, 1), (2527, 2), (2831, -1)]

def row652 : Integer.Sparse (Fin 3237) := [(1455, 1), (2099, 1), (2462, 1), (2507, 1), (2527, 1), (2528, 1), (2831, -1)]

def row653 : Integer.Sparse (Fin 3237) := [(2094, 1), (2096, 1), (2099, 1), (2100, 1), (2185, 1), (2527, 1), (2831, -1)]

def row654 : Integer.Sparse (Fin 3237) := [(1468, 1), (2185, 1), (2465, 1), (2527, 1), (2536, 1), (2538, 1), (2831, -1)]

def row655 : Integer.Sparse (Fin 3237) := [(2119, 1), (2469, 1), (2505, 1), (2507, 1), (2527, 2), (2831, -1)]

def row656 : Integer.Sparse (Fin 3237) := [(0, 301), (32, -110), (160, -160), (225, 40), (261, -395), (821, -2160), (822, -4320), (826, -2160), (2046, -2160), (2047, -4320), (2050, -2160), (2081, -4320), (2177, -4320), (2302, -2160), (2303, -4320), (2309, -2160), (2317, -2160), (2553, -2160), (2555, -4320), (2566, -2160), (2569, -2160), (2570, -6480), (2572, -4320), (2573, -4320), (2575, -4320), (2578, -4320), (2762, -2160), (2768, -2160)]

def row657 : Integer.Sparse (Fin 3237) := [(0, -133), (32, 55), (160, 80), (261, 160), (821, 1080), (822, 2160), (826, 1080), (2046, 1080), (2047, 2160), (2050, 1080), (2081, 2160), (2177, 2160)]

def row658 : Integer.Sparse (Fin 3237) := [(0, 677), (32, -165), (160, -240), (256, 160), (261, 90), (652, -4320), (653, -4320), (654, -8640), (691, -4320), (1141, -4320), (1142, -4320), (1143, -4320), (1156, -8640), (1752, -4320), (1753, -8640), (1780, -4320), (1932, -8640), (1933, -8640), (1934, -8640), (1948, -8640), (2429, -4320), (2430, -4320), (2437, -8640), (2489, -8640), (2490, -8640), (2491, -8640), (2501, -8640), (2553, -4320), (2554, -4320), (2557, -8640), (2570, -4320), (2571, -4320), (2575, -8640), (2802, -4320)]

def row659 : Integer.Sparse (Fin 3237) := [(0, -181), (32, 55), (160, 80), (261, -80), (652, 1440), (653, 1440), (654, 2880), (691, 1440), (1752, 1440), (1753, 2880), (1780, 1440), (1932, 2880), (1933, 2880), (1934, 2880), (1948, 2880)]

def row660 : Integer.Sparse (Fin 3237) := [(0, 179), (32, 175), (160, 80), (261, 160), (1591, -8640), (1592, -4320), (1593, -4320), (1610, -4320), (1618, -4320), (1932, -12960), (1948, -8640), (1968, -8640), (2159, -4320), (2489, -12960), (2491, -8640), (2536, -8640), (2567, -4320), (2570, -12960), (2571, -4320), (3179, 17280), (3189, 34560), (3194, 34560), (3197, 34560)]

def row661 : Integer.Sparse (Fin 3237) := [(2489, 1), (2491, 2), (2570, 1), (2831, -1)]

def row662 : Integer.Sparse (Fin 3237) := [(1591, 1), (2526, 2), (2570, 2), (2831, -1)]

def row663 : Integer.Sparse (Fin 3237) := [(0, -252), (32, -200), (255, 160), (256, 160), (261, 180), (773, 8640), (774, 8640), (775, 8640), (779, 8640), (863, 8640), (2014, 8640), (2015, 8640), (2016, 8640), (2017, 8640), (2066, 8640), (2067, 8640), (2069, 8640), (2095, 8640), (2133, 8640), (2134, 8640), (2135, 8640), (2145, 8640), (2146, 8640), (2147, 8640), (2157, 8640), (2158, 8640), (2161, 8640), (2186, 8640), (2492, 8640), (2699, 8640), (2718, 8640)]

def row664 : Integer.Sparse (Fin 3237) := [(0, -88), (32, -60), (160, -240), (162, -80), (225, -160), (256, -80), (261, 180), (1738, 4320), (1739, 4320), (1740, 4320), (1783, 4320), (1951, 4320), (2012, 4320), (2013, 4320), (2017, 4320), (2147, 4320), (2249, 4320), (2250, 4320), (2256, 4320), (2313, 4320), (2484, 4320), (2491, 4320), (2492, 4320), (2498, 4320), (2513, 4320), (2514, 4320), (2516, 4320), (2522, 4320), (2527, 4320), (2528, 4320), (2532, 4320), (2538, 4320), (2539, 4320), (2738, 4320)]

def row665 : Integer.Sparse (Fin 3237) := [(852, 1), (853, 1), (854, 1), (856, 1), (863, 1), (1973, 1), (2840, -1)]

def row666 : Integer.Sparse (Fin 3237) := [(0, 18), (32, 5), (160, -80), (256, -80), (261, -25), (2047, -2160), (2160, -2160), (2572, -2160), (2574, -2160), (2727, -4320), (2729, -2160), (2742, -2160), (2769, -2160), (2783, -2160), (2786, -2160), (2923, 8640), (2924, 8640), (2925, 8640), (2928, 8640), (2933, 8640), (3110, 8640), (3111, 8640), (3113, 8640), (3116, 8640), (3133, 8640), (3137, 8640), (3146, 8640), (3147, 8640), (3148, 8640), (3162, 8640), (3163, 8640), (3164, 8640), (3177, 8640), (3178, 8640), (3181, 8640), (3195, 8640), (3197, 8640), (3198, 8640), (3229, 8640)]

def row667 : Integer.Sparse (Fin 3237) := [(0, -232), (3, -40), (4, 10), (32, -90), (159, 480), (160, 160), (162, 160), (165, -160), (225, 160), (256, 160), (261, 100), (274, 480), (665, 8640), (666, 8640), (667, 8640), (671, 8640), (682, 8640), (1762, 8640), (1763, 8640), (1766, 8640), (1772, 8640), (1867, 8640), (1868, 8640), (1869, 8640), (1900, 8640), (1901, 8640), (1902, 8640), (1904, 8640), (1938, 8640), (1939, 8640), (1942, 8640), (1944, 8640), (1973, 8640), (1974, 8640), (1978, 8640), (2727, 8640), (2737, 8640), (2742, 8640)]

def row668 : Integer.Sparse (Fin 3237) := [(0, -80), (32, -45), (160, -240), (225, -80), (252, 240), (255, -160), (256, -80), (261, 175), (1082, 4320), (1083, 4320), (1084, 4320), (1093, 4320), (1150, 4320), (2078, 4320), (2086, 4320), (2096, 4320), (2187, 4320), (2358, 4320), (2359, 4320), (2374, 4320), (2411, 4320), (2417, 4320), (2434, 4320), (2467, 4320), (2468, 4320), (2498, 4320), (2524, 4320), (2525, 4320), (2528, 4320), (2533, 4320), (2539, 4320), (2572, 4320), (2574, 4320), (2783, 4320), (2789, 4320)]

def row669 : Integer.Sparse (Fin 3237) := [(2157, 1), (2725, 1), (2727, 1), (2729, 1), (2769, 1), (2786, 1), (2840, -1)]

def row670 : Integer.Sparse (Fin 3237) := [(909, 1), (911, 1), (912, 1), (915, 1), (946, 1), (2157, 1), (2840, -1)]

def row671 : Integer.Sparse (Fin 3237) := [(909, 1), (2044, 1), (2144, 1), (2151, 1), (2157, 2), (2840, -1)]

def row672 : Integer.Sparse (Fin 3237) := [(1823, 1), (2107, 1), (2108, 1), (2110, 1), (2157, 1), (2725, 1), (2840, -1)]

def row673 : Integer.Sparse (Fin 3237) := [(2044, 1), (2047, 1), (2048, 1), (2051, 1), (2157, 1), (2786, 1), (2840, -1)]

def row674 : Integer.Sparse (Fin 3237) := [(1825, 1), (2151, 1), (2152, 1), (2153, 1), (2157, 1), (2727, 1), (2840, -1)]

def row675 : Integer.Sparse (Fin 3237) := [(0, -242), (3, -40), (32, -220), (68, -160), (160, -1440), (162, -320), (224, 480), (225, -480), (255, -480), (256, -480), (260, 120), (261, -170), (1479, 8640), (1480, 8640), (1483, 8640), (1492, 8640), (1573, 8640), (1598, 8640), (1615, 8640), (1616, 8640), (1618, 8640), (1818, 8640), (1825, 8640), (1833, 8640), (1937, 8640), (1938, 8640), (1940, 8640), (1955, 8640), (1957, 8640), (1960, 8640), (1961, 8640), (1967, 8640), (1968, 8640), (1972, 8640), (1973, 17280), (2183, 8640), (2189, 8640)]

def row676 : Integer.Sparse (Fin 3237) := [(2086, 1), (2356, 1), (2360, 1), (2373, 1), (2491, 1), (2528, 1), (2831, -1)]

def row677 : Integer.Sparse (Fin 3237) := [(1450, 1), (2083, 1), (2506, 1), (2522, 1), (2526, 1), (2528, 1), (2831, -1)]

def row678 : Integer.Sparse (Fin 3237) := [(1453, 1), (2085, 1), (2205, 1), (2208, 1), (2214, 1), (2528, 1), (2831, -1)]

def row679 : Integer.Sparse (Fin 3237) := [(2083, 1), (2085, 1), (2086, 1), (2099, 1), (2179, 1), (2528, 1), (2831, -1)]

def row680 : Integer.Sparse (Fin 3237) := [(1471, 1), (2179, 1), (2467, 1), (2528, 2), (2536, 1), (2831, -1)]

def row681 : Integer.Sparse (Fin 3237) := [(2208, 1), (2360, 1), (2506, 1), (2507, 1), (2528, 2), (2831, -1)]

def row682 : Integer.Sparse (Fin 3237) := [(0, 17), (32, -5), (160, 80), (225, 40), (256, 80), (261, -50), (2046, -720), (2050, -2160), (2566, -720), (2569, -2160), (2767, -720), (2768, -2160), (2797, -720), (2926, 2880), (2927, 8640), (2936, 2880), (3112, 8640), (3118, 2880), (3179, 8640), (3180, 17280), (3184, 8640)]

def row683 : Integer.Sparse (Fin 3237) := [(0, -17), (32, 5), (160, -80), (225, -40), (256, -80), (261, 50), (1137, 720), (1138, 720), (1144, 2160), (2164, 720), (2176, 2160), (2431, 2160), (2484, 2160), (2492, 4320), (2566, 720), (2569, 2160), (2797, 720)]

def row684 : Integer.Sparse (Fin 3237) := [(2159, 1), (2767, 1), (2768, 3), (2839, -1)]

def row685 : Integer.Sparse (Fin 3237) := [(1953, 1), (2109, 3), (2159, 1), (2767, 1), (2839, -1)]

def row686 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1593, -4320), (1618, -4320), (1895, -1440), (1907, -4320), (2369, -1440), (2373, -4320), (2570, -4320), (3058, 5760), (3059, 17280), (3063, 5760), (3064, 5760), (3179, 17280), (3191, 17280), (3197, 34560)]

def row687 : Integer.Sparse (Fin 3237) := [(0, -73), (32, -60), (160, -240), (162, -240), (225, -80), (261, 45), (1584, 1440), (1585, 1440), (1594, 4320), (1895, 1440), (1907, 4320), (2133, 4320), (2145, 4320), (2157, 8640), (2240, 1440)]

def row688 : Integer.Sparse (Fin 3237) := [(0, -23), (32, 50), (160, 400), (162, 80), (225, 280), (256, 240), (261, -175), (1733, 2160), (1736, 4320), (1779, 2160), (1947, 2160), (2288, 2160), (2292, 2160), (2299, 4320), (2489, 4320), (2496, 2160), (2523, 4320), (2524, 4320), (2526, 4320), (2529, 4320), (2531, 2160), (2535, 2160), (2536, 4320), (2746, 4320)]

def row689 : Integer.Sparse (Fin 3237) := [(1957, 1), (2746, 2), (2762, 1), (2767, 1), (2768, 1), (2839, -1)]

def row690 : Integer.Sparse (Fin 3237) := [(833, 1), (834, 1), (836, 1), (843, 2), (1957, 1), (2839, -1)]

def row691 : Integer.Sparse (Fin 3237) := [(843, 1), (1867, 1), (1932, 1), (1957, 2), (1968, 1), (2839, -1)]

def row692 : Integer.Sparse (Fin 3237) := [(1859, 1), (1860, 1), (1862, 1), (1867, 1), (1957, 1), (2746, 1), (2839, -1)]

def row693 : Integer.Sparse (Fin 3237) := [(0, 49), (32, -5), (160, 80), (256, 160), (261, -50), (2081, -8640), (2177, -4320), (2555, -8640), (2573, -4320), (2726, -4320), (2741, -4320), (2791, -17280), (2794, -4320), (2907, 17280), (2908, 17280), (2910, 17280), (2917, 34560), (3128, 34560), (3129, 34560), (3134, 34560), (3155, 17280), (3156, 17280), (3159, 34560), (3169, 17280), (3170, 17280), (3174, 34560), (3190, 17280), (3194, 34560)]

def row694 : Integer.Sparse (Fin 3237) := [(0, -115), (3, -160), (4, 20), (32, 260), (66, 320), (68, 160), (71, 160), (159, -480), (160, 1040), (162, 240), (165, 160), (225, 240), (255, 160), (256, 320), (261, -525), (274, -480), (632, 4320), (633, 4320), (635, 4320), (646, 8640), (1819, 8640), (1820, 8640), (1834, 8640), (1888, 4320), (1889, 4320), (1893, 8640), (1923, 4320), (1924, 4320), (1930, 8640), (1958, 4320), (1967, 8640), (2726, 4320)]

def row695 : Integer.Sparse (Fin 3237) := [(0, -48), (32, 50), (160, 640), (225, 320), (252, -240), (255, 160), (256, 320), (261, -230), (1079, 4320), (1080, 8640), (1086, 4320), (1148, 4320), (2355, 4320), (2356, 8640), (2367, 4320), (2464, 4320), (2465, 8640), (2496, 4320), (2512, 8640), (2513, 8640), (2517, 8640), (2527, 8640), (2535, 4320), (2555, 8640), (2573, 4320), (2791, 8640)]

def row696 : Integer.Sparse (Fin 3237) := [(2175, 1), (2741, 1), (2791, 2), (2794, 1), (2839, -1)]

def row697 : Integer.Sparse (Fin 3237) := [(923, 1), (924, 1), (926, 1), (934, 2), (2175, 1), (2839, -1)]

def row698 : Integer.Sparse (Fin 3237) := [(2081, 1), (2082, 1), (2084, 1), (2095, 1), (2175, 1), (2791, 1), (2839, -1)]

def row699 : Integer.Sparse (Fin 3237) := [(2171, 1), (2172, 1), (2175, 1), (2183, 2), (2741, 1), (2839, -1)]

def row700 : Integer.Sparse (Fin 3237) := [(0, -197), (3, 20), (32, -230), (68, 80), (160, 80), (224, -240), (255, 160), (256, 160), (260, -60), (261, -145), (1588, 4320), (1589, 4320), (1591, 4320), (1598, 8640), (1818, 8640), (1824, 4320), (1831, 4320), (1954, 4320), (1956, 4320), (1957, 8640), (1960, 8640), (1961, 8640), (1967, 8640), (1968, 8640), (1973, 8640)]

def row701 : Integer.Sparse (Fin 3237) := [(2080, 1), (2458, 1), (2491, 2), (2526, 1), (2831, -1)]

def row702 : Integer.Sparse (Fin 3237) := [(1449, 1), (1450, 2), (1466, 1), (1591, 1), (2526, 1), (2831, -1)]

def row703 : Integer.Sparse (Fin 3237) := [(2080, 1), (2083, 2), (2094, 1), (2174, 1), (2526, 1), (2831, -1)]

def row704 : Integer.Sparse (Fin 3237) := [(1466, 1), (2174, 1), (2526, 2), (2536, 2), (2831, -1)]

def row705 : Integer.Sparse (Fin 3237) := [(2505, 1), (2506, 2), (2526, 2), (2831, -1)]

def row706 : Integer.Sparse (Fin 3237) := [(0, 117), (32, 55), (160, 80), (225, 80), (261, -170), (790, -2160), (821, -1440), (2023, -4320), (2046, -1440), (2177, -4320), (2291, -2160), (2302, -1440), (2566, -1440), (2568, -4320), (2570, -4320), (2573, -4320), (2767, -1440), (2797, -1440)]

def row707 : Integer.Sparse (Fin 3237) := [(0, -82), (32, -55), (160, -80), (225, -40), (261, 95), (790, 2160), (821, 1440), (2023, 4320), (2046, 1440), (2177, 4320), (2797, 1440)]

def row708 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1591, -4320), (1918, -2160), (2159, -1440), (2458, -2160), (2567, -1440), (2570, -4320), (3063, 5760), (3189, 17280), (3191, 17280)]

def row709 : Integer.Sparse (Fin 3237) := [(0, -60), (32, -95), (160, 80), (162, 160), (225, 40), (261, -95), (1918, 2160), (2133, 4320), (2159, 1440), (2175, 4320), (2240, 1440)]

def row710 : Integer.Sparse (Fin 3237) := [(0, 17), (32, -5), (160, 80), (225, 40), (256, 80), (261, -50), (865, -1080), (1836, -1080), (1932, -1080), (1934, -2160), (1968, -2160), (2314, -1080), (2489, -1080), (2501, -2160), (2518, -1080), (2536, -2160), (2726, -1080), (2741, -1080), (2749, -2160), (2768, -2160), (2965, 4320), (2966, 4320), (2967, 8640), (3129, 8640), (3132, 4320), (3146, 4320), (3148, 8640), (3150, 4320), (3184, 8640), (3189, 8640), (3190, 8640)]

def row711 : Integer.Sparse (Fin 3237) := [(0, -75), (32, 85), (160, 240), (255, 160), (256, 160), (261, -180), (819, 1440), (820, 1440), (823, 2880), (2044, 1440), (2045, 1440), (2048, 2880), (2080, 1440), (2082, 2880), (2175, 2880), (2176, 2880), (2178, 2880)]

def row712 : Integer.Sparse (Fin 3237) := [(0, -17), (32, 5), (160, -80), (225, -40), (256, -80), (261, 50), (1916, 1080), (1917, 1080), (1921, 1080), (1947, 2160), (2299, 1080), (2304, 2160), (2314, 1080), (2489, 1080), (2501, 2160), (2517, 2160), (2518, 1080), (2524, 1080), (2526, 2160), (2533, 2160), (2535, 2160), (2536, 2160), (2741, 1080), (2749, 1080)]

def row713 : Integer.Sparse (Fin 3237) := [(1968, 1), (2726, 1), (2749, 1), (2768, 2), (2839, -1)]

def row714 : Integer.Sparse (Fin 3237) := [(843, 1), (845, 2), (849, 1), (865, 1), (1968, 1), (2839, -1)]

def row715 : Integer.Sparse (Fin 3237) := [(865, 1), (1836, 1), (1968, 3), (2839, -1)]

def row716 : Integer.Sparse (Fin 3237) := [(1867, 1), (1869, 2), (1873, 1), (1968, 1), (2749, 1), (2839, -1)]

def row717 : Integer.Sparse (Fin 3237) := [(0, 380), (4, -5), (32, -65), (66, 80), (160, 80), (225, 80), (256, -320), (261, -500), (648, -4320), (649, -8640), (657, -4320), (685, -4320), (1088, -4320), (1089, -8640), (1092, -4320), (1163, -4320), (1750, -8640), (1756, -4320), (1775, -4320), (1836, -4320), (1837, -8640), (1895, -4320), (1896, -8640), (1907, -4320), (1968, -8640), (1969, -8640), (1979, -8640), (2369, -4320), (2370, -8640), (2373, -4320), (2414, -8640), (2416, -4320), (2445, -4320), (2518, -4320), (2519, -8640), (2536, -8640), (2537, -8640), (2538, -8640), (2562, -4320), (2578, -8640), (2768, -4320), (2794, -4320)]

def row718 : Integer.Sparse (Fin 3237) := [(0, -254), (4, 5), (32, 55), (66, -80), (160, 80), (256, 160), (261, 340), (648, 4320), (649, 8640), (657, 4320), (685, 4320), (1750, 8640), (1756, 4320), (1775, 4320), (1836, 4320), (1837, 8640), (1895, 4320), (1896, 8640), (1907, 4320), (1968, 8640), (1969, 8640), (1979, 8640), (2768, 4320)]

def row719 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 10), (261, 15), (1466, -360), (1468, -720), (1471, -360), (1589, -360), (1608, -720), (1616, -360), (1932, -360), (1948, -720), (1968, -360), (1979, -720), (2489, -360), (2491, -720), (2536, -360), (2538, -720), (2570, -720), (2571, -360), (3174, 2880), (3177, 1440), (3184, 1440), (3187, 1440), (3188, 1440), (3189, 2880), (3193, 2880), (3194, 2880), (3197, 2880)]

def row720 : Integer.Sparse (Fin 3237) := [(0, -200), (32, -200), (160, -320), (255, -160), (256, -160), (261, -160), (1589, 4320), (1608, 8640), (1616, 4320), (1930, 8640), (1932, 4320), (1938, 4320), (1954, 4320), (1955, 4320), (1957, 8640), (1959, 4320), (1964, 8640), (1967, 8640), (1968, 4320), (1973, 8640), (1979, 8640)]

def row721 : Integer.Sparse (Fin 3237) := [(0, 29), (32, -45), (160, -240), (225, -160), (256, -160), (261, 90), (821, -2160), (1753, -4320), (1756, -2160), (1932, -4320), (1934, -4320), (1968, -2160), (2302, -2160), (2437, -4320), (2445, -2160), (2489, -4320), (2501, -4320), (2536, -2160), (2726, -2160), (2741, -2160), (2762, -4320), (2959, 8640), (2960, 17280), (2965, 8640), (3142, 17280), (3143, 8640), (3146, 8640), (3170, 17280), (3189, 17280)]

def row722 : Integer.Sparse (Fin 3237) := [(0, -129), (3, -320), (4, 35), (32, 300), (66, 320), (68, 160), (71, 400), (160, 1200), (165, 160), (225, 320), (252, -120), (255, 240), (256, 560), (261, -510), (801, 2160), (802, 4320), (819, 2160), (2029, 2160), (2030, 4320), (2044, 2160), (2168, 4320), (2175, 4320)]

def row723 : Integer.Sparse (Fin 3237) := [(0, -29), (32, 45), (160, 240), (225, 160), (256, 160), (261, -90), (2298, 2160), (2299, 2160), (2300, 4320), (2302, 2160), (2437, 4320), (2445, 2160), (2487, 4320), (2489, 4320), (2494, 2160), (2496, 4320), (2501, 4320), (2524, 2160), (2526, 4320), (2536, 2160), (2726, 2160)]

def row724 : Integer.Sparse (Fin 3237) := [(821, 1), (1932, 3), (2839, -1)]

def row725 : Integer.Sparse (Fin 3237) := [(1852, 2), (1854, 1), (1867, 1), (1932, 1), (2741, 1), (2839, -1)]

def row726 : Integer.Sparse (Fin 3237) := [(0, 458), (4, 15), (32, -55), (66, -80), (71, -160), (160, -80), (256, 160), (261, -180), (598, -8640), (600, -4320), (617, -4320), (652, -4320), (1047, -8640), (1049, -4320), (1064, -4320), (1141, -4320), (1680, -8640), (1681, -4320), (1694, -4320), (1808, -8640), (1810, -4320), (1913, -8640), (1918, -4320), (1932, -4320), (1933, -8640), (1934, -8640), (1948, -8640), (2331, -8640), (2332, -4320), (2342, -4320), (2456, -8640), (2458, -4320), (2475, -8640), (2480, -4320), (2489, -4320), (2490, -8640), (2491, -8640), (2501, -8640), (2553, -4320), (2570, -8640), (2782, -8640), (2802, -4320)]

def row727 : Integer.Sparse (Fin 3237) := [(0, -324), (4, -15), (32, 55), (66, 80), (71, 160), (160, 80), (261, 30), (598, 8640), (600, 4320), (617, 4320), (652, 4320), (1680, 8640), (1681, 4320), (1694, 4320), (1808, 8640), (1810, 4320), (1913, 8640), (1918, 4320), (1932, 4320), (1933, 8640), (1934, 8640), (1948, 8640), (2782, 4320)]

def row728 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1389, -2880), (1392, -1440), (1560, -2880), (1567, -1440), (1895, -1440), (1932, -5760), (1948, -2880), (1968, -1440), (2369, -1440), (2489, -5760), (2491, -2880), (2536, -1440), (2570, -4320), (3159, 11520), (3162, 5760), (3174, 11520), (3177, 5760), (3179, 17280)]

def row729 : Integer.Sparse (Fin 3237) := [(0, -175), (32, -135), (160, 560), (255, 320), (256, 320), (261, -380), (1560, 8640), (1567, 4320), (1893, 8640), (1895, 4320), (1900, 4320), (1930, 8640), (1932, 8640), (1938, 4320), (1940, 8640), (1948, 8640), (1968, 4320), (2145, 4320)]

def row730 : Integer.Sparse (Fin 3237) := [(0, 33), (32, 10), (160, -160), (225, -80), (256, -80), (261, 25), (866, -2160), (1837, -4320), (1948, -4320), (1950, -2160), (1969, -2160), (2315, -2160), (2491, -4320), (2503, -2160), (2519, -4320), (2537, -2160), (2729, -4320), (2742, -4320), (2766, -2160), (2769, -2160), (2971, 17280), (2972, 8640), (2973, 8640), (3134, 17280), (3136, 17280), (3137, 17280), (3185, 8640), (3194, 17280), (3195, 8640), (3197, 17280), (3198, 8640)]

def row731 : Integer.Sparse (Fin 3237) := [(0, -106), (32, -30), (160, -160), (255, -160), (256, -160), (261, 100), (863, 2880), (864, 1440), (867, 1440), (2095, 2880), (2096, 2880), (2098, 2880), (2157, 2880), (2158, 1440), (2161, 1440), (2186, 2880), (2187, 1440)]

def row732 : Integer.Sparse (Fin 3237) := [(0, -33), (32, -10), (160, 160), (225, 80), (256, 80), (261, -25), (1944, 4320), (1946, 2160), (1951, 2160), (1978, 2160), (2313, 4320), (2315, 2160), (2316, 2160), (2491, 4320), (2503, 2160), (2513, 4320), (2519, 4320), (2520, 4320), (2527, 4320), (2528, 4320), (2537, 2160), (2539, 2160), (2742, 4320)]

def row733 : Integer.Sparse (Fin 3237) := [(0, 28), (32, -7), (160, 16), (256, 48), (261, -31), (685, -864), (686, -432), (687, -432), (695, -432), (1092, -864), (1094, -432), (1097, -432), (1165, -432), (1775, -864), (1776, -1728), (1777, -864), (1784, -864), (1789, -432), (1907, -864), (1908, -432), (1909, -432), (1968, -864), (1969, -432), (1979, -864), (1980, -864), (2373, -864), (2376, -432), (2416, -864), (2418, -864), (2447, -864), (2536, -864), (2537, -432), (2538, -864), (2578, -432), (2579, -432), (2769, -432), (2793, -1728)]

def row734 : Integer.Sparse (Fin 3237) := [(0, -39), (32, 20), (160, -80), (256, -80), (261, 35), (685, 2160), (686, 1080), (687, 1080), (695, 1080), (1775, 2160), (1776, 2160), (1777, 2160), (1784, 2160), (1907, 2160), (1908, 1080), (1909, 1080), (1968, 2160), (1969, 1080), (1979, 2160), (1980, 1080), (2769, 1080), (2793, 2160)]

def row735 : Integer.Sparse (Fin 3237) := [(0, 19), (32, 5), (160, -80), (261, 110), (1468, -2160), (1473, -1080), (1477, -1080), (1608, -2160), (1628, -1080), (1629, -1080), (1948, -2160), (1968, -2160), (1979, -2160), (2491, -2160), (2536, -2160), (2538, -2160), (2571, -2160), (3137, 8640), (3138, 4320), (3174, 8640), (3183, 8640), (3193, 8640), (3194, 17280), (3195, 8640), (3199, 4320)]

def row736 : Integer.Sparse (Fin 3237) := [(0, -102), (32, -50), (160, 480), (255, 160), (256, 160), (261, -420), (1608, 8640), (1628, 4320), (1629, 4320), (1930, 8640), (1944, 8640), (1945, 8640), (1948, 8640), (1964, 8640), (1965, 4320), (1967, 8640), (1968, 8640), (1970, 4320), (1976, 4320), (1978, 4320), (1979, 4320), (2186, 8640)]

def row737 : Integer.Sparse (Fin 3237) := [(0, 1), (261, -1), (2317, -48), (2318, -24), (2319, -48), (2553, -48), (2557, -96), (2562, -48), (2570, -96), (2575, -48), (2578, -48)]

def row738 : Integer.Sparse (Fin 3237) := [(0, 84), (32, 45), (160, 240), (225, 160), (256, 80), (261, -195), (822, -4320), (1780, -4320), (1782, -4320), (1784, -4320), (1808, -4320), (1933, -4320), (1948, -4320), (1950, -4320), (1979, -4320), (2303, -4320), (2430, -4320), (2439, -4320), (2447, -4320), (2475, -4320), (2490, -4320), (2491, -4320), (2503, -4320), (2538, -4320), (2717, -4320), (2722, -4320), (2764, -4320), (2765, -4320), (2965, 17280), (2967, 17280), (2968, 17280), (2971, 17280), (3125, 17280), (3134, 17280), (3175, 17280), (3179, 17280), (3180, 17280), (3181, 17280), (3194, 17280), (3197, 17280)]

def row739 : Integer.Sparse (Fin 3237) := [(0, -84), (32, -45), (160, -240), (225, -160), (256, -80), (261, 195), (2299, 4320), (2303, 4320), (2304, 4320), (2306, 4320), (2313, 4320), (2430, 4320), (2439, 4320), (2447, 4320), (2475, 4320), (2477, 4320), (2484, 4320), (2490, 4320), (2491, 4320), (2492, 4320), (2497, 4320), (2498, 4320), (2503, 4320), (2513, 4320), (2527, 4320), (2528, 4320), (2538, 4320), (2717, 4320)]

def row740 : Integer.Sparse (Fin 3237) := [(0, 6), (32, 1), (261, -1), (617, -72), (618, -72), (619, -72), (622, -72), (691, -72), (1049, -72), (1051, -72), (1054, -72), (1069, -72), (1143, -72), (1694, -72), (1695, -72), (1696, -72), (1698, -72), (1734, -144), (1735, -72), (1737, -72), (1741, -72), (1780, -72), (1781, -72), (1918, -72), (1919, -72), (1920, -72), (1932, -72), (1933, -72), (1934, -72), (1948, -144), (1949, -144), (1950, -72), (2332, -72), (2335, -72), (2346, -72), (2402, -72), (2408, -72), (2430, -72), (2458, -72), (2460, -72), (2489, -72), (2490, -72), (2491, -144), (2501, -72), (2503, -72), (2570, -72), (2571, -72), (2783, -72), (2786, -72), (2791, -144), (2794, -72)]

def row741 : Integer.Sparse (Fin 3237) := [(0, -198), (32, -65), (160, 80), (256, 80), (261, -95), (617, 4320), (618, 4320), (619, 4320), (622, 4320), (691, 4320), (1694, 4320), (1695, 4320), (1696, 4320), (1698, 4320), (1734, 4320), (1735, 4320), (1737, 4320), (1780, 4320), (1918, 4320), (1919, 4320), (1920, 4320), (1932, 4320), (1933, 4320), (1934, 4320), (1948, 8640), (1949, 4320), (1950, 4320), (2786, 4320), (2791, 4320), (2794, 4320)]

def row742 : Integer.Sparse (Fin 3237) := [(0, 17), (32, 13), (160, -16), (261, 40), (1389, -864), (1394, -864), (1398, -864), (1560, -864), (1577, -864), (1578, -864), (1907, -864), (1918, -864), (1932, -864), (1948, -2592), (1968, -864), (1979, -864), (2373, -864), (2458, -864), (2489, -864), (2491, -2592), (2536, -864), (2538, -864), (2570, -864), (2571, -864), (3132, 3456), (3133, 3456), (3137, 3456), (3159, 3456), (3166, 3456), (3174, 3456), (3183, 3456), (3184, 3456), (3189, 3456), (3194, 3456), (3197, 3456)]

def row743 : Integer.Sparse (Fin 3237) := [(0, -106), (32, -90), (160, -160), (255, -160), (256, -160), (261, -200), (1560, 4320), (1577, 4320), (1578, 4320), (1893, 4320), (1904, 4320), (1905, 4320), (1907, 4320), (1916, 4320), (1918, 4320), (1930, 4320), (1932, 4320), (1944, 4320), (1945, 4320), (1947, 4320), (1948, 12960), (1979, 4320), (2157, 4320), (2175, 4320), (2186, 4320)]

def row744 : Integer.Sparse (Fin 3237) := [(821, -1), (826, -3), (865, -1), (1810, -3), (1836, -1), (1932, -3), (1934, -6), (1968, -3), (2302, -1), (2309, -3), (2314, -1), (2480, -3), (2489, -3), (2501, -6), (2518, -1), (2536, -3), (2839, 4)]

def row745 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (1895, -1440), (1907, -4320), (1918, -4320), (1932, -4320), (1948, -8640), (2159, -1440), (2369, -1440), (2373, -4320), (2458, -4320), (2489, -4320), (2491, -8640), (2567, -1440), (2570, -4320), (2831, 5760)]

def row746 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (652, -4320), (1141, -4320), (1466, -4320), (1589, -4320), (1591, -8640), (1592, -4320), (1593, -4320), (1610, -4320), (1618, -4320), (2570, -4320), (2910, 17280), (3047, 17280), (3048, 34560), (3063, 17280), (3189, 17280)]

def row747 : Integer.Sparse (Fin 3237) := [(0, -47), (32, -55), (160, -80), (261, 20), (1141, 4320), (1148, 4320), (1588, 4320), (1589, 4320), (1591, 4320), (1598, 8640), (1600, 4320), (1610, 4320), (1618, 4320), (1957, 4320)]

def row748 : Integer.Sparse (Fin 3237) := [(0, 64), (32, -45), (160, -240), (225, -120), (256, -160), (261, 15), (468, -2160), (469, -4320), (486, -4320), (1388, -4320), (1389, -8640), (1420, -4320), (1548, -4320), (1549, -4320), (1560, -8640), (1592, -4320), (1610, -4320), (2762, -4320)]

def row749 : Integer.Sparse (Fin 3237) := [(0, 47), (32, 55), (160, 80), (261, -20), (652, -2160), (654, -4320), (657, -2160), (1141, -2160), (1156, -4320), (1163, -2160), (1389, -4320), (1392, -2160), (1466, -2160), (1468, -4320), (1471, -2160), (1560, -4320), (1567, -2160), (1589, -2160), (1591, -8640), (1592, -4320), (1593, -4320), (1608, -4320), (1610, -4320), (1616, -2160), (1618, -4320), (1932, -2160), (1968, -2160), (2489, -2160), (2536, -2160), (2570, -4320), (2831, 8640)]

def row750 : Integer.Sparse (Fin 3237) := [(0, -1), (261, 1), (2816, 16), (2817, 24), (2827, 16), (2828, 48), (2831, 48), (2832, 48), (2839, 16)]

def row751 : Integer.Sparse (Fin 3237) := [(0, -44), (32, 10), (160, 560), (162, 80), (225, 320), (256, 240), (261, -170), (1297, 4320), (1299, 4320), (1304, 4320), (1313, 4320), (1601, 4320), (2103, 4320), (2107, 4320), (2116, 4320), (2128, 4320), (2433, 4320), (2434, 4320), (2441, 4320), (2486, 4320), (2582, 4320), (2584, 4320), (2661, 4320), (2662, 4320), (2675, 4320), (2678, 4320), (2683, 4320), (2693, 4320), (2694, 4320), (2695, 4320), (2696, 4320), (2703, 4320), (2704, 4320)]

def row752 : Integer.Sparse (Fin 3237) := [(1754, 1), (2608, 1), (2683, 1), (2696, 1), (2698, 1), (2699, 1), (2840, -1)]

def row753 : Integer.Sparse (Fin 3237) := [(1747, 1), (1748, 1), (1754, 1), (1766, 1), (1927, 1), (2696, 1), (2840, -1)]

def row754 : Integer.Sparse (Fin 3237) := [(1766, 1), (1927, 1), (2615, 1), (2696, 1), (2702, 1), (2704, 1), (2840, -1)]

def row755 : Integer.Sparse (Fin 3237) := [(2239, 1), (2603, 1), (2608, 1), (2615, 1), (2683, 1), (2696, 1), (2840, -1)]

def row756 : Integer.Sparse (Fin 3237) := [(1748, 2), (2603, 2), (2696, 2), (2840, -1)]

def row757 : Integer.Sparse (Fin 3237) := [(0, 48), (32, 25), (160, 80), (256, 80), (261, -35), (2633, -4320), (2677, -8640), (2689, -4320), (2690, -8640), (2699, -4320), (2703, -4320), (2704, -8640), (2716, -8640), (2717, -4320), (2722, -4320), (2764, -4320), (3029, 17280), (3030, 17280), (3032, 17280), (3036, 17280), (3048, 17280), (3123, 17280), (3125, 17280), (3130, 17280), (3175, 17280), (3207, 17280), (3208, 17280), (3210, 17280), (3213, 17280), (3216, 34560), (3224, 17280), (3225, 17280), (3227, 17280), (3229, 17280), (3230, 17280), (3231, 17280)]

def row758 : Integer.Sparse (Fin 3237) := [(0, -179), (4, -5), (32, -40), (66, 160), (68, 160), (159, -240), (160, 1520), (162, 240), (165, 80), (218, -480), (219, -240), (222, -240), (224, -480), (225, 480), (252, -480), (255, 400), (256, 480), (260, 60), (261, -20), (1432, 4320), (1433, 4320), (1439, 4320), (1450, 4320), (1554, 4320), (2074, 4320), (2079, 4320), (2088, 4320), (2182, 4320), (2629, 4320), (2632, 4320), (2636, 4320), (2637, 4320), (2652, 4320), (2662, 4320), (2690, 4320), (2704, 4320), (2720, 4320), (2736, 4320), (2739, 4320), (2743, 4320), (2746, 4320), (2789, 4320)]

def row759 : Integer.Sparse (Fin 3237) := [(0, -204), (3, 80), (4, -10), (32, -70), (68, 160), (159, -480), (160, 640), (162, 160), (165, 160), (224, -480), (225, 480), (255, 160), (256, 320), (260, -120), (261, -160), (1399, 8640), (1400, 8640), (1403, 8640), (1412, 8640), (1598, 8640), (2476, 8640), (2477, 8640), (2497, 8640), (2515, 8640), (2612, 8640), (2613, 8640), (2615, 8640), (2689, 8640), (2690, 8640), (2703, 8640), (2708, 8640), (2709, 8640), (2712, 8640), (2713, 17280), (2716, 8640), (2717, 8640), (2720, 8640), (2728, 8640), (2737, 8640), (2746, 8640)]

def row760 : Integer.Sparse (Fin 3237) := [(2677, 1), (2718, 1), (2776, 1), (2795, 1), (2796, 1), (2840, -1)]

def row761 : Integer.Sparse (Fin 3237) := [(2223, 1), (2629, 1), (2636, 1), (2639, 1), (2718, 1), (2795, 1), (2840, -1)]

def row762 : Integer.Sparse (Fin 3237) := [(1821, 1), (2639, 1), (2675, 1), (2710, 1), (2718, 1), (2725, 1), (2840, -1)]

def row763 : Integer.Sparse (Fin 3237) := [(2224, 1), (2633, 1), (2677, 1), (2699, 1), (2718, 1), (2796, 1), (2840, -1)]

def row764 : Integer.Sparse (Fin 3237) := [(1811, 1), (2636, 1), (2677, 1), (2718, 1), (2720, 1), (2722, 1), (2840, -1)]

def row765 : Integer.Sparse (Fin 3237) := [(2227, 1), (2637, 1), (2710, 1), (2718, 1), (2743, 1), (2776, 1), (2840, -1)]

def row766 : Integer.Sparse (Fin 3237) := [(1803, 1), (2629, 1), (2633, 1), (2637, 1), (2716, 1), (2718, 1), (2840, -1)]

def row767 : Integer.Sparse (Fin 3237) := [(2234, 1), (2675, 1), (2677, 1), (2704, 1), (2718, 1), (2720, 1), (2840, -1)]

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

def row768 : Integer.Sparse (Fin 3237) := [(1802, 1), (2223, 1), (2224, 1), (2227, 1), (2234, 1), (2718, 1), (2840, -1)]

def row769 : Integer.Sparse (Fin 3237) := [(0, -57), (3, 40), (4, -5), (32, 160), (68, 80), (159, -240), (160, 1280), (162, 320), (165, 80), (224, -240), (225, 240), (255, 240), (256, 480), (260, -60), (261, -470), (274, -240), (1362, 4320), (1365, 4320), (1369, 4320), (1402, 4320), (1553, 4320), (1793, 4320), (1795, 4320), (1819, 4320), (1888, 4320), (2493, 4320), (2494, 4320), (2496, 4320), (2529, 4320), (2599, 4320), (2614, 4320), (2645, 4320), (2661, 4320), (2700, 4320), (2702, 4320), (2707, 4320), (2719, 8640), (2725, 4320), (2726, 4320), (2737, 4320), (2746, 4320)]

def row770 : Integer.Sparse (Fin 3237) := [(2737, 1), (2738, 1), (2741, 1), (2746, 1), (2762, 1), (2791, 1), (2839, -1)]

def row771 : Integer.Sparse (Fin 3237) := [(1848, 1), (2076, 1), (2233, 1), (2235, 1), (2238, 1), (2738, 1), (2839, -1)]

def row772 : Integer.Sparse (Fin 3237) := [(2235, 1), (2738, 2), (2744, 1), (2760, 1), (2788, 1), (2839, -1)]

def row773 : Integer.Sparse (Fin 3237) := [(1849, 1), (2090, 1), (2678, 1), (2730, 1), (2737, 1), (2738, 1), (2839, -1)]

def row774 : Integer.Sparse (Fin 3237) := [(2238, 1), (2678, 1), (2684, 1), (2694, 1), (2738, 1), (2789, 1), (2839, -1)]

def row775 : Integer.Sparse (Fin 3237) := [(1860, 1), (2077, 1), (2731, 1), (2738, 1), (2744, 1), (2746, 1), (2839, -1)]

def row776 : Integer.Sparse (Fin 3237) := [(2233, 1), (2730, 1), (2731, 1), (2738, 2), (2770, 1), (2839, -1)]

def row777 : Integer.Sparse (Fin 3237) := [(1854, 1), (2172, 1), (2684, 1), (2738, 2), (2741, 1), (2839, -1)]

def row778 : Integer.Sparse (Fin 3237) := [(2076, 1), (2077, 1), (2084, 1), (2090, 1), (2172, 1), (2738, 1), (2839, -1)]

def row779 : Integer.Sparse (Fin 3237) := [(0, -50), (32, -5), (160, 80), (225, 40), (261, 25), (2066, 2160), (2067, 2160), (2069, 2160), (2095, 2160), (2157, 2160), (2403, 2160), (2409, 2160), (2434, 2160), (2478, 2160), (2492, 2160), (2498, 2160), (2514, 2160), (2626, 2160), (2628, 2160), (2641, 2160), (2662, 2160), (2688, 2160), (2699, 2160), (2711, 2160), (2717, 2160), (2720, 2160), (2723, 2160), (2738, 2160), (2743, 2160), (2789, 2160)]

def row780 : Integer.Sparse (Fin 3237) := [(0, -176), (3, 20), (4, -5), (32, -40), (159, -240), (160, 400), (165, 80), (225, 80), (255, 80), (256, 160), (261, 145), (274, -240), (1730, 4320), (1731, 4320), (1738, 4320), (1766, 4320), (1942, 4320), (2065, 4320), (2069, 4320), (2147, 4320), (2513, 4320), (2514, 4320), (2516, 4320), (2528, 4320), (2598, 4320), (2615, 4320), (2628, 4320), (2638, 4320), (2717, 4320), (2718, 4320), (2720, 4320), (2732, 4320), (2737, 4320), (2742, 4320), (2743, 4320)]

def row781 : Integer.Sparse (Fin 3237) := [(1834, 1), (2641, 1), (2719, 1), (2722, 1), (2725, 1), (2729, 1), (2840, -1)]

def row782 : Integer.Sparse (Fin 3237) := [(1826, 2), (2640, 1), (2719, 2), (2728, 1), (2840, -1)]

def row783 : Integer.Sparse (Fin 3237) := [(2107, 1), (2675, 1), (2676, 1), (2703, 1), (2719, 1), (2725, 1), (2840, -1)]

def row784 : Integer.Sparse (Fin 3237) := [(2104, 1), (2631, 1), (2634, 1), (2640, 1), (2641, 1), (2719, 1), (2840, -1)]

def row785 : Integer.Sparse (Fin 3237) := [(1805, 1), (1827, 1), (2631, 1), (2675, 1), (2719, 1), (2720, 1), (2840, -1)]

def row786 : Integer.Sparse (Fin 3237) := [(0, -104), (3, 40), (4, -5), (32, -5), (68, 80), (159, -240), (160, 640), (162, 80), (165, 80), (224, -240), (225, 240), (255, 160), (256, 400), (260, -60), (261, -40), (1363, 4320), (1364, 4320), (1371, 4320), (1403, 4320), (1554, 4320), (2065, 4320), (2067, 4320), (2088, 4320), (2146, 4320), (2477, 4320), (2478, 4320), (2498, 4320), (2516, 4320), (2598, 4320), (2615, 4320), (2626, 4320), (2637, 4320), (2662, 4320), (2690, 4320), (2704, 4320), (2713, 4320), (2717, 4320), (2718, 4320), (2719, 4320), (2738, 8640)]

def row787 : Integer.Sparse (Fin 3237) := [(0, 111), (32, -5), (160, 80), (225, 200), (261, 640), (1471, -2160), (1473, -1080), (1476, -1080), (1616, -2160), (1617, -1080), (1620, -2160), (1628, -1080), (2097, -2160), (2556, -2160), (2563, -1080), (2579, -1080), (2643, -2160), (2684, -2160), (2700, -2160), (2701, -2160), (2704, -4320), (2749, -4320), (2750, -2160), (2752, -2160), (2754, -1080), (2763, -2160), (2766, -3240)]

def row788 : Integer.Sparse (Fin 3237) := [(0, -57), (32, 5), (160, -80), (225, -80), (261, -310), (1471, 1440), (1473, 720), (1476, 720), (1620, 720), (2097, 1440), (2643, 1440), (2684, 1440), (2704, 1440), (2749, 1440), (2750, 720), (2766, 720)]

def row789 : Integer.Sparse (Fin 3237) := [(0, 211), (32, -5), (160, 80), (225, 80), (256, -160), (261, -260), (1424, -4320), (1426, -2160), (1429, -2160), (1569, -4320), (1571, -2160), (1580, -2160), (1611, -2160), (1619, -2160), (1896, -4320), (1909, -2160), (1969, -2160), (2047, -4320), (2055, -2160), (2370, -4320), (2376, -2160), (2537, -2160), (2572, -4320), (2577, -2160), (2578, -2160), (2622, -4320), (2669, -4320), (2677, -4320), (2690, -4320), (2699, -4320), (2703, -4320), (2729, -4320), (2742, -4320), (2765, -4320), (2768, -4320), (2769, -4320)]

def row790 : Integer.Sparse (Fin 3237) := [(0, -75), (32, 5), (160, -80), (225, -80), (261, 140), (1424, 2160), (1426, 1080), (1429, 1080), (1611, 1080), (2047, 2160), (2055, 1080), (2370, 2160), (2376, 1080), (2537, 1080), (2622, 2160), (2677, 2160), (2699, 2160), (2729, 2160), (2769, 1080)]

def row791 : Integer.Sparse (Fin 3237) := [(0, 69), (32, 30), (225, 80), (256, -80), (261, -135), (1950, -2160), (1979, -2160), (2160, -2160), (2503, -2160), (2538, -2160), (2574, -2160), (2699, -4320), (2703, -4320), (2723, -8640), (2729, -4320), (2742, -4320), (2765, -4320), (2766, -2160), (2769, -2160), (3180, 17280), (3181, 17280), (3182, 8640), (3185, 8640), (3197, 17280), (3198, 17280), (3226, 17280), (3230, 17280)]

def row792 : Integer.Sparse (Fin 3237) := [(0, -51), (32, -25), (160, -80), (225, -80), (261, 110), (1942, 1440), (1943, 720), (1951, 720), (2147, 1440), (2161, 720), (2528, 1440), (2538, 720), (2539, 720), (2738, 1440), (2742, 1440), (2743, 1440)]

def row793 : Integer.Sparse (Fin 3237) := [(0, 641), (32, -100), (160, -320), (256, -400), (261, -685), (1756, -4320), (1758, -4320), (1760, -4320), (1784, -4320), (2087, -4320), (2445, -4320), (2446, -4320), (2447, -4320), (2449, -4320), (2557, -4320), (2561, -4320), (2575, -4320), (2578, -4320), (2609, -4320), (2610, -4320), (2622, -4320), (2635, -4320), (2667, -4320), (2668, -4320), (2669, -4320), (2715, -4320), (2729, -4320), (2742, -4320), (2753, -4320), (2757, -4320), (2761, -4320), (2762, -4320), (2764, -8640), (2765, -4320), (2769, -4320), (2788, -4320), (2793, -8640)]

def row794 : Integer.Sparse (Fin 3237) := [(0, -132), (32, 25), (160, 80), (256, 80), (261, 145), (1756, 1080), (1758, 1080), (1760, 1080), (1784, 1080), (2087, 1080), (2609, 1080), (2610, 1080), (2622, 1080), (2635, 1080), (2742, 1080), (2788, 1080), (2793, 1080)]

def row795 : Integer.Sparse (Fin 3237) := [(0, 355), (32, -40), (160, -80), (225, 80), (256, -80), (261, 125), (1389, -2160), (1391, -2160), (1398, -2160), (1422, -2160), (1560, -2160), (1561, -2160), (1562, -2160), (1578, -2160), (1592, -2160), (1610, -2160), (1808, -2160), (1815, -2160), (1933, -2160), (2475, -2160), (2481, -2160), (2490, -2160), (2554, -2160), (2607, -2160), (2611, -2160), (2621, -2160), (2664, -2160), (2665, -2160), (2671, -2160), (2674, -2160), (2676, -2160), (2688, -2160), (2691, -2160), (2693, -2160), (2698, -2160), (2717, -2160), (2722, -2160), (2723, -4320), (2757, -2160), (2759, -2160), (2762, -2160), (2763, -4320), (2764, -4320), (2802, -2160), (2803, -2160)]

def row796 : Integer.Sparse (Fin 3237) := [(0, -36), (32, 5), (160, 16), (256, 16), (261, -19), (1389, 288), (1391, 288), (1398, 288), (1422, 288), (1592, 288), (1808, 288), (1815, 288), (1933, 288), (2607, 288), (2611, 288), (2621, 288), (2674, 288), (2676, 288), (2693, 288), (2717, 288), (2723, 288), (2763, 288)]

def row797 : Integer.Sparse (Fin 3237) := [(0, 186), (32, 85), (160, 80), (225, 160), (256, -80), (261, -305), (1933, -4320), (1948, -4320), (2490, -4320), (2491, -4320), (2693, -4320), (2694, -4320), (2698, -4320), (2699, -8640), (2702, -4320), (2703, -8640), (2704, -8640), (2716, -8640), (2717, -4320), (2722, -4320), (2727, -8640), (2764, -4320), (2765, -4320), (2769, -4320), (2783, -4320), (2786, -4320), (2803, -4320), (3175, 17280), (3194, 17280), (3226, 17280), (3228, 17280), (3229, 17280), (3230, 17280), (3232, 17280)]

def row798 : Integer.Sparse (Fin 3237) := [(0, -84), (32, -35), (160, 80), (256, 80), (261, 85), (2182, 1080), (2186, 1080), (2694, 1080), (2699, 1080), (2704, 1080), (2738, 1080), (2743, 1080), (2780, 1080), (2783, 1080), (2784, 1080), (2789, 1080)]

def row799 : Integer.Sparse (Fin 3237) := [(0, 573), (32, -70), (160, -320), (225, -560), (256, 240), (261, -115), (1392, -4320), (1394, -4320), (1397, -4320), (1424, -4320), (1567, -4320), (1568, -4320), (1569, -4320), (1577, -4320), (1593, -4320), (1618, -4320), (2081, -4320), (2087, -4320), (2555, -4320), (2561, -4320), (2562, -4320), (2578, -4320), (2609, -4320), (2610, -4320), (2622, -4320), (2633, -4320), (2667, -4320), (2668, -4320), (2669, -4320), (2677, -4320), (2689, -4320), (2690, -4320), (2694, -4320), (2702, -4320), (2726, -4320), (2727, -8640), (2729, -4320), (2741, -4320), (2742, -4320), (2752, -4320), (2758, -4320), (2762, -4320), (2764, -4320), (2765, -8640), (2766, -4320), (2768, -4320)]

def row800 : Integer.Sparse (Fin 3237) := [(0, -36), (32, 5), (160, 40), (225, 40), (261, 5), (1392, 360), (1394, 360), (1397, 360), (1424, 360), (1593, 360), (2081, 360), (2087, 360), (2609, 360), (2610, 360), (2622, 360), (2633, 360), (2677, 360), (2694, 360), (2726, 360), (2727, 360), (2729, 360), (2768, 360)]

def row801 : Integer.Sparse (Fin 3237) := [(0, 96), (32, 45), (225, -80), (256, 80), (261, -15), (1948, -4320), (2491, -4320), (2694, -4320), (2699, -4320), (2702, -4320), (2703, -4320), (2704, -8640), (2717, -4320), (2722, -4320), (2764, -4320), (2765, -2160), (2766, -4320), (3179, 17280), (3180, 17280), (3181, 17280), (3197, 17280), (3226, 17280), (3227, 8640)]

def row802 : Integer.Sparse (Fin 3237) := [(0, -224), (32, -150), (160, -160), (225, 320), (255, -160), (256, -320), (261, -110), (1688, 8640), (1689, 8640), (1690, 8640), (1699, 8640), (1942, 8640), (2069, 8640), (2070, 8640), (2098, 8640), (2161, 8640), (2338, 8640), (2339, 8640), (2347, 8640), (2498, 8640), (2514, 8640), (2520, 8640), (2539, 8640), (2628, 8640), (2644, 8640), (2718, 8640), (2723, 8640), (2734, 8640), (2735, 8640), (2738, 8640), (2742, 8640), (2743, 8640), (2778, 8640)]

def row803 : Integer.Sparse (Fin 3237) := [(1838, 1), (2644, 1), (2706, 1), (2723, 1), (2728, 1), (2729, 1), (2840, -1)]

def row804 : Integer.Sparse (Fin 3237) := [(0, -500), (3, -80), (32, -200), (159, 960), (160, -1920), (162, -640), (224, 960), (225, -320), (256, -960), (260, 240), (261, 300), (274, 960), (1400, 17280), (1401, 17280), (1408, 17280), (1418, 17280), (1599, 17280), (1843, 17280), (1845, 17280), (1868, 17280), (1901, 17280), (2485, 17280), (2495, 17280), (2497, 17280), (2530, 17280), (2613, 17280), (2616, 17280), (2675, 17280), (2695, 17280), (2701, 17280), (2703, 17280), (2709, 17280), (2713, 17280), (2719, 17280), (2724, 17280), (2727, 17280), (2747, 34560)]

def row805 : Integer.Sparse (Fin 3237) := [(0, -351), (3, -60), (32, -225), (160, -1680), (162, -240), (218, 720), (219, 720), (225, -720), (252, 1440), (255, -240), (256, -720), (260, 180), (261, 330), (1439, 12960), (1441, 12960), (1442, 12960), (1469, 12960), (1570, 12960), (2028, 12960), (2033, 12960), (2042, 12960), (2182, 12960), (2354, 12960), (2359, 12960), (2365, 12960), (2525, 12960), (2636, 12960), (2652, 12960), (2662, 12960), (2669, 12960), (2670, 12960), (2683, 12960), (2704, 12960), (2738, 12960), (2739, 12960), (2748, 12960), (2780, 12960), (2783, 12960), (2784, 12960)]

def row806 : Integer.Sparse (Fin 3237) := [(1856, 1), (2038, 1), (2227, 1), (2230, 1), (2236, 1), (2743, 1), (2840, -1)]

def row807 : Integer.Sparse (Fin 3237) := [(2230, 1), (2643, 1), (2683, 1), (2699, 1), (2743, 1), (2784, 1), (2840, -1)]

def row808 : Integer.Sparse (Fin 3237) := [(1870, 1), (2039, 1), (2616, 1), (2710, 1), (2743, 1), (2748, 1), (2840, -1)]

def row809 : Integer.Sparse (Fin 3237) := [(1853, 1), (2036, 1), (2615, 1), (2683, 1), (2740, 1), (2743, 1), (2840, -1)]

def row810 : Integer.Sparse (Fin 3237) := [(2051, 1), (2622, 1), (2743, 1), (2776, 1), (2784, 1), (2786, 1), (2840, -1)]

def row811 : Integer.Sparse (Fin 3237) := [(2236, 1), (2615, 1), (2616, 1), (2622, 1), (2704, 1), (2743, 1), (2840, -1)]

def row812 : Integer.Sparse (Fin 3237) := [(1857, 1), (2153, 1), (2637, 1), (2643, 1), (2727, 1), (2743, 1), (2840, -1)]

def row813 : Integer.Sparse (Fin 3237) := [(0, 127), (32, 5), (160, -80), (225, 240), (261, 770), (1315, -4320), (1316, -4320), (1318, -4320), (1329, -4320), (1620, -4320), (2068, -4320), (2071, -4320), (2097, -4320), (2160, -4320), (2552, -4320), (2556, -4320), (2560, -4320), (2574, -4320), (2585, -4320), (2586, -4320), (2627, -4320), (2643, -4320), (2684, -4320), (2700, -4320), (2701, -4320), (2704, -12960), (2760, -4320), (2763, -4320), (2766, -4320)]

def row814 : Integer.Sparse (Fin 3237) := [(0, 84), (32, 45), (160, 240), (225, 160), (256, 80), (261, -195), (1784, -4320), (2447, -4320), (2622, -4320), (2669, -4320), (2677, -4320), (2690, -4320), (2694, -4320), (2699, -12960), (2702, -4320), (2703, -12960), (2704, -8640), (2764, -4320), (2765, -4320), (3032, 17280), (3033, 17280), (3035, 17280), (3040, 17280), (3065, 17280), (3113, 17280), (3115, 17280), (3173, 17280), (3175, 17280), (3181, 34560), (3192, 17280), (3210, 34560), (3211, 17280), (3221, 17280), (3226, 17280), (3227, 17280), (3230, 17280)]

def row815 : Integer.Sparse (Fin 3237) := [(0, -124), (32, -95), (160, -640), (162, -240), (225, -320), (256, -160), (261, 265), (1554, 4320), (1555, 4320), (1563, 4320), (1570, 4320), (1601, 4320), (2128, 4320), (2135, 4320), (2146, 4320), (2182, 4320), (2434, 4320), (2447, 4320), (2448, 4320), (2498, 4320), (2662, 8640), (2669, 4320), (2670, 4320), (2690, 4320), (2694, 4320), (2696, 4320), (2699, 4320), (2703, 4320), (2720, 4320), (2738, 4320), (2743, 4320)]

def row816 : Integer.Sparse (Fin 3237) := [(0, 67), (32, -15), (160, 240), (225, 160), (256, 160), (261, 90), (2717, -8640), (2722, -8640), (2726, -8640), (2741, -8640), (2763, -4320), (2768, -4320), (2782, -8640), (3089, 17280), (3090, 17280), (3091, 34560), (3092, 17280), (3093, 34560), (3094, 17280), (3129, 34560), (3170, 17280), (3179, 17280), (3190, 17280), (3215, 34560), (3222, 17280), (3225, 34560), (3232, 34560), (3235, 34560)]

def row817 : Integer.Sparse (Fin 3237) := [(0, -93), (32, 155), (160, 2000), (225, 800), (252, -480), (255, 480), (256, 1120), (261, -820), (1678, 4320), (1679, 4320), (1682, 8640), (1924, 4320), (2072, 4320), (2082, 8640), (2178, 4320), (2330, 4320), (2333, 8640), (2484, 4320), (2634, 8640), (2735, 4320), (2776, 8640), (2781, 8640), (2782, 4320), (2784, 8640)]

def row818 : Integer.Sparse (Fin 3237) := [(0, -67), (32, 95), (160, 80), (225, -80), (256, 160), (261, -410), (274, -480), (1685, 4320), (1686, 8640), (1692, 4320), (1940, 4320), (2336, 4320), (2337, 8640), (2341, 4320), (2496, 4320), (2517, 8640), (2535, 4320), (2706, 4320), (2711, 8640), (2722, 8640), (2739, 8640), (2741, 8640), (2748, 8640), (2777, 8640)]

def row819 : Integer.Sparse (Fin 3237) := [(2724, 1), (2777, 2), (2778, 1), (2782, 1), (2839, -1)]

def row820 : Integer.Sparse (Fin 3237) := [(1820, 1), (2638, 1), (2709, 1), (2717, 1), (2724, 1), (2726, 1), (2839, -1)]

def row821 : Integer.Sparse (Fin 3237) := [(0, 47), (32, -55), (160, -80), (256, -160), (261, 230), (2609, -8640), (2642, -4320), (2667, -8640), (2694, -4320), (2702, -4320), (2726, -4320), (2733, -4320), (2741, -4320), (2767, -4320), (2782, -17280), (2797, -4320), (2802, -4320), (3019, 17280), (3023, 17280), (3025, 34560), (3054, 17280), (3139, 17280), (3141, 34560), (3167, 17280), (3204, 17280), (3205, 34560), (3215, 34560), (3222, 34560), (3228, 34560), (3229, 34560)]

def row822 : Integer.Sparse (Fin 3237) := [(0, -297), (3, -240), (32, 1290), (66, 480), (71, 480), (159, -2880), (160, 6960), (162, 720), (218, -1440), (222, -1440), (224, -2880), (225, 2880), (256, 3840), (260, 720), (261, -3765), (274, -2880), (1377, 12960), (1381, 12960), (1386, 25920), (1582, 12960), (1846, 12960), (1851, 25920), (1914, 12960), (2602, 12960), (2605, 25920), (2706, 25920), (2711, 25920), (2724, 25920), (2725, 25920), (2733, 12960), (2741, 12960), (2767, 12960)]

def row823 : Integer.Sparse (Fin 3237) := [(0, -56), (3, 60), (32, 90), (66, 80), (160, 2080), (162, 160), (218, -720), (219, -480), (225, 1280), (252, -960), (255, 160), (256, 1120), (260, -180), (261, -990), (1435, 4320), (1437, 8640), (1465, 4320), (1566, 4320), (2453, 4320), (2455, 4320), (2483, 8640), (2634, 8640), (2650, 8640), (2666, 4320), (2667, 8640), (2702, 4320), (2735, 8640), (2737, 8640), (2740, 8640), (2782, 8640)]

def row824 : Integer.Sparse (Fin 3237) := [(2726, 1), (2780, 1), (2782, 2), (2802, 1), (2839, -1)]

def row825 : Integer.Sparse (Fin 3237) := [(2026, 1), (2228, 2), (2229, 1), (2237, 1), (2780, 1), (2839, -1)]

def row826 : Integer.Sparse (Fin 3237) := [(2229, 1), (2642, 1), (2780, 3), (2797, 1), (2839, -1)]

def row827 : Integer.Sparse (Fin 3237) := [(2027, 1), (2602, 1), (2773, 2), (2780, 1), (2839, -1)]

def row828 : Integer.Sparse (Fin 3237) := [(2228, 1), (2638, 1), (2773, 1), (2778, 1), (2780, 1), (2789, 1), (2839, -1)]

def row829 : Integer.Sparse (Fin 3237) := [(2031, 1), (2609, 1), (2778, 1), (2780, 2), (2782, 1), (2839, -1)]

def row830 : Integer.Sparse (Fin 3237) := [(2237, 1), (2602, 1), (2609, 2), (2694, 1), (2780, 1), (2839, -1)]

def row831 : Integer.Sparse (Fin 3237) := [(2138, 1), (2638, 2), (2642, 1), (2726, 1), (2780, 1), (2839, -1)]

def row832 : Integer.Sparse (Fin 3237) := [(2026, 1), (2027, 1), (2031, 2), (2138, 1), (2780, 1), (2839, -1)]

def row833 : Integer.Sparse (Fin 3237) := [(0, -204), (3, 40), (32, -95), (159, -480), (160, 560), (162, 240), (224, -240), (225, 400), (260, -60), (261, -35), (1843, 8640), (1844, 4320), (1867, 4320), (1900, 4320), (2483, 4320), (2485, 8640), (2521, 4320), (2675, 8640), (2692, 4320), (2693, 4320), (2695, 8640), (2727, 8640), (2728, 8640), (2744, 4320), (2747, 8640)]

def row834 : Integer.Sparse (Fin 3237) := [(0, -531), (3, 120), (4, -15), (32, -315), (66, 240), (68, 240), (160, 1680), (162, 240), (218, -720), (219, -720), (225, 960), (255, 480), (256, 480), (260, -180), (261, 255), (2028, 25920), (2031, 12960), (2040, 12960), (2354, 25920), (2358, 12960), (2363, 12960), (2524, 12960), (2658, 12960), (2659, 12960), (2662, 25920), (2683, 25920), (2694, 12960), (2743, 25920), (2783, 25920), (2784, 25920)]

def row835 : Integer.Sparse (Fin 3237) := [(2044, 1), (2620, 1), (2740, 1), (2786, 2), (2840, -1)]

def row836 : Integer.Sparse (Fin 3237) := [(1866, 1), (2035, 1), (2614, 1), (2740, 1), (2748, 2), (2840, -1)]

def row837 : Integer.Sparse (Fin 3237) := [(2681, 1), (2683, 2), (2698, 1), (2740, 1), (2840, -1)]

def row838 : Integer.Sparse (Fin 3237) := [(2035, 1), (2036, 2), (2044, 1), (2151, 1), (2740, 1), (2840, -1)]

def row839 : Integer.Sparse (Fin 3237) := [(1851, 1), (2151, 1), (2681, 1), (2727, 2), (2740, 1), (2840, -1)]

def row840 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (225, -40), (256, -80), (261, 80), (1756, -2160), (2445, -2160), (2609, -2160), (2667, -2160), (2684, -2160), (2693, -1080), (2694, -2160), (2698, -1080), (2700, -2160), (2702, -2160), (2760, -2160), (2762, -1080), (2767, -1080), (2797, -1080), (2802, -1080), (3020, 4320), (3023, 4320), (3026, 8640), (3063, 4320), (3105, 4320), (3170, 4320), (3204, 4320), (3206, 8640), (3226, 8640), (3228, 4320), (3229, 8640)]

def row841 : Integer.Sparse (Fin 3237) := [(0, -218), (3, -160), (4, 10), (32, 505), (66, 640), (68, 480), (71, 160), (159, -960), (160, 3680), (162, 1040), (165, 320), (218, -960), (219, -480), (222, -480), (224, -960), (225, 1600), (252, -480), (255, 320), (256, 1440), (260, 120), (261, -1315), (1378, 4320), (1381, 4320), (1390, 8640), (1583, 4320), (2114, 4320), (2168, 4320), (2602, 4320), (2608, 8640), (2718, 8640), (2724, 4320), (2725, 8640), (2760, 4320), (2767, 4320)]

def row842 : Integer.Sparse (Fin 3237) := [(0, -61), (32, 175), (160, 1520), (162, 480), (225, 640), (256, 800), (261, -800), (1553, 8640), (1559, 4320), (1566, 4320), (1600, 4320), (2444, 4320), (2445, 8640), (2496, 4320), (2661, 8640), (2666, 4320), (2667, 8640), (2698, 4320), (2700, 8640), (2702, 8640), (2719, 8640), (2737, 8640), (2740, 4320)]

def row843 : Integer.Sparse (Fin 3237) := [(0, 84), (32, 45), (160, 240), (225, 160), (256, 80), (261, -195), (1780, -2160), (2430, -2160), (2620, -2160), (2658, -2160), (2693, -4320), (2694, -2160), (2698, -4320), (2699, -4320), (2702, -2160), (2703, -4320), (2704, -8640), (2764, -4320), (2765, -4320), (3112, 8640), (3113, 17280), (3173, 17280), (3179, 17280), (3191, 8640), (3209, 8640), (3210, 17280), (3221, 17280), (3228, 8640)]

def row844 : Integer.Sparse (Fin 3237) := [(0, -319), (3, 60), (4, -10), (32, -135), (68, 80), (159, -480), (160, -400), (162, -400), (165, 160), (224, -240), (225, -400), (255, 160), (256, 160), (260, -60), (261, 510), (274, -480), (2107, 8640), (2109, 4320), (2145, 4320), (2484, 4320), (2486, 8640), (2522, 4320), (2675, 8640), (2693, 4320), (2694, 4320), (2696, 8640), (2724, 4320), (2744, 4320)]

def row845 : Integer.Sparse (Fin 3237) := [(0, -86), (32, -15), (160, 240), (162, 160), (225, 80), (256, 80), (261, 75), (2128, 4320), (2133, 2160), (2145, 2160), (2430, 2160), (2431, 2160), (2434, 4320), (2484, 2160), (2658, 2160), (2659, 2160), (2662, 4320), (2693, 2160), (2696, 4320), (2699, 4320), (2704, 4320), (2780, 2160)]

def row846 : Integer.Sparse (Fin 3237) := [(1780, 1), (2620, 1), (2698, 1), (2702, 1), (2840, -1)]

def row847 : Integer.Sparse (Fin 3237) := [(0, -156), (32, 240), (160, 640), (225, 160), (256, 800), (261, -1060), (274, -480), (1794, 8640), (1795, 8640), (1797, 8640), (1834, 8640), (1893, 8640), (2404, 8640), (2407, 8640), (2433, 8640), (2487, 8640), (2493, 8640), (2497, 8640), (2523, 8640), (2645, 8640), (2661, 8640), (2697, 8640), (2698, 8640), (2719, 8640), (2725, 8640), (2726, 8640), (2729, 8640), (2745, 8640), (2746, 8640), (2748, 8640), (2771, 8640), (2792, 8640)]

def row848 : Integer.Sparse (Fin 3237) := [(2095, 1), (2737, 1), (2771, 1), (2791, 1), (2792, 1), (2793, 1), (2839, -1)]

def row849 : Integer.Sparse (Fin 3237) := [(2116, 1), (2678, 1), (2682, 1), (2693, 1), (2737, 1), (2792, 1), (2839, -1)]

def row850 : Integer.Sparse (Fin 3237) := [(1852, 1), (2183, 1), (2682, 1), (2737, 1), (2741, 1), (2742, 1), (2839, -1)]

def row851 : Integer.Sparse (Fin 3237) := [(0, 47), (32, -55), (160, -80), (256, -160), (261, 230), (2635, -4320), (2684, -4320), (2694, -4320), (2700, -4320), (2702, -4320), (2715, -4320), (2717, -4320), (2722, -4320), (2761, -4320), (2767, -4320), (2788, -4320), (2791, -8640), (2797, -4320), (2802, -4320), (3024, 17280), (3025, 17280), (3026, 17280), (3037, 17280), (3047, 17280), (3123, 17280), (3124, 17280), (3128, 17280), (3169, 17280), (3205, 17280), (3206, 17280), (3212, 17280), (3214, 17280), (3215, 17280), (3222, 17280), (3223, 17280), (3226, 17280), (3228, 17280), (3229, 34560), (3236, 17280)]

def row852 : Integer.Sparse (Fin 3237) := [(0, -178), (4, -10), (32, 600), (66, 480), (68, 320), (159, -480), (160, 4960), (162, 320), (165, 160), (218, -480), (222, -960), (224, -960), (225, 1600), (255, 960), (256, 2880), (260, 120), (261, -2180), (274, -480), (1431, 8640), (1434, 8640), (1437, 8640), (1449, 8640), (1553, 8640), (1803, 8640), (1807, 8640), (1819, 8640), (1923, 8640), (2630, 8640), (2634, 8640), (2648, 8640), (2650, 8640), (2661, 8640), (2700, 8640), (2702, 8640), (2707, 8640), (2719, 8640), (2735, 8640), (2737, 17280), (2740, 8640), (2792, 8640)]

def row853 : Integer.Sparse (Fin 3237) := [(0, -237), (3, 120), (4, -15), (32, 330), (66, 240), (68, 240), (160, 2640), (162, 1440), (218, -720), (219, -720), (225, 1200), (252, -720), (256, 960), (260, -180), (261, -1590), (1384, 12960), (1386, 12960), (1390, 12960), (1413, 12960), (1588, 12960), (2461, 12960), (2464, 12960), (2476, 12960), (2512, 12960), (2605, 12960), (2608, 12960), (2617, 12960), (2706, 12960), (2711, 12960), (2714, 12960), (2715, 12960), (2718, 12960), (2721, 12960), (2722, 12960), (2724, 12960), (2725, 25920), (2761, 12960), (2767, 12960), (2791, 12960), (2792, 12960)]

def row854 : Integer.Sparse (Fin 3237) := [(2074, 1), (2630, 1), (2635, 1), (2638, 1), (2717, 1), (2789, 1), (2839, -1)]

def row855 : Integer.Sparse (Fin 3237) := [(2225, 1), (2635, 1), (2788, 1), (2789, 2), (2797, 1), (2839, -1)]

def row856 : Integer.Sparse (Fin 3237) := [(2169, 1), (2684, 1), (2778, 1), (2789, 2), (2839, -1)]

def row857 : Integer.Sparse (Fin 3237) := [(0, 84), (32, 35), (160, -80), (256, -80), (261, -85), (2676, -4320), (2688, -4320), (2699, -4320), (2703, -4320), (2716, -8640), (2717, -4320), (2722, -4320), (2727, -8640), (2729, -4320), (2742, -4320), (2764, -4320), (2769, -4320), (2783, -4320), (2786, -4320), (3110, 17280), (3111, 17280), (3113, 17280), (3116, 17280), (3128, 17280), (3130, 17280), (3134, 17280), (3194, 17280), (3197, 17280), (3207, 17280), (3208, 17280), (3210, 17280), (3216, 17280), (3217, 17280), (3224, 17280), (3225, 17280), (3226, 34560), (3232, 17280)]

def row858 : Integer.Sparse (Fin 3237) := [(0, -179), (3, 20), (4, -5), (32, -35), (159, -240), (160, 160), (165, 80), (261, 205), (1762, 4320), (1763, 4320), (1766, 4320), (1772, 4320), (1973, 4320), (2512, 4320), (2513, 4320), (2515, 4320), (2527, 4320), (2612, 4320), (2613, 4320), (2615, 4320), (2709, 4320), (2713, 4320), (2716, 4320), (2717, 4320), (2719, 4320), (2727, 4320), (2732, 4320), (2736, 4320), (2738, 4320), (2742, 4320), (2747, 4320)]

def row859 : Integer.Sparse (Fin 3237) := [(0, -336), (32, -190), (160, 800), (225, 160), (255, 160), (256, 320), (261, 250), (2078, 8640), (2079, 8640), (2084, 8640), (2095, 8640), (2186, 8640), (2411, 8640), (2417, 8640), (2434, 8640), (2528, 8640), (2632, 8640), (2636, 8640), (2641, 8640), (2652, 8640), (2662, 8640), (2688, 8640), (2699, 8640), (2718, 8640), (2738, 8640), (2739, 8640), (2783, 8640), (2784, 8640), (2795, 8640)]

def row860 : Integer.Sparse (Fin 3237) := [(2676, 1), (2725, 1), (2776, 1), (2786, 1), (2840, -1)]

def row861 : Integer.Sparse (Fin 3237) := [(2110, 1), (2637, 1), (2639, 1), (2641, 1), (2725, 1), (2776, 1), (2840, -1)]

def row862 : Integer.Sparse (Fin 3237) := [(2108, 1), (2708, 1), (2710, 1), (2725, 1), (2748, 1), (2840, -1)]

def row863 : Integer.Sparse (Fin 3237) := [(0, 52), (32, -3), (160, 48), (256, 80), (261, -51), (1784, -864), (1786, -432), (1789, -432), (1907, -864), (1908, -432), (1909, -432), (1979, -432), (2050, -864), (2055, -432), (2373, -864), (2376, -432), (2447, -864), (2451, -432), (2538, -432), (2569, -864), (2575, -432), (2577, -432), (2579, -432), (2622, -864), (2669, -864), (2761, -864), (2764, -864), (2766, -432), (2768, -864), (2769, -864), (2788, -864), (2793, -1728)]

def row864 : Integer.Sparse (Fin 3237) := [(0, -72), (32, 5), (160, -80), (256, -80), (261, 65), (1784, 1440), (1786, 720), (1789, 720), (2050, 1440), (2055, 720), (2373, 1440), (2376, 720), (2538, 720), (2622, 1440), (2788, 1440), (2793, 1440)]

def row865 : Integer.Sparse (Fin 3237) := [(0, 137), (32, -5), (160, 80), (225, -80), (256, 80), (261, -50), (1468, -2160), (1470, -1080), (1477, -1080), (1608, -2160), (1609, -1080), (1611, -1080), (1619, -1080), (1629, -1080), (1837, -2160), (1969, -1080), (2519, -2160), (2537, -1080), (2563, -1080), (2682, -2160), (2685, -2160), (2697, -2160), (2699, -2160), (2703, -2160), (2705, -2160), (2729, -2160), (2742, -2160), (2753, -2160), (2755, -1080), (2766, -1080), (2768, -2160), (2769, -1080), (2794, -2160)]

def row866 : Integer.Sparse (Fin 3237) := [(0, -72), (32, 5), (160, -80), (256, -80), (261, 65), (1468, 1440), (1470, 720), (1477, 720), (1619, 720), (1837, 1440), (1969, 720), (2682, 1440), (2685, 1440), (2703, 1440), (2742, 1440), (2766, 720)]

def row867 : Integer.Sparse (Fin 3237) := [(0, 63), (32, 30), (225, -80), (256, 80), (261, 15), (1969, -2160), (1979, -2160), (2160, -2160), (2537, -2160), (2538, -2160), (2574, -2160), (2699, -4320), (2703, -4320), (2727, -8640), (2729, -4320), (2742, -4320), (2750, -4320), (2764, -4320), (2766, -2160), (2783, -4320), (2786, -4320), (2787, -4320), (3194, 17280), (3195, 8640), (3197, 17280), (3198, 8640), (3229, 17280), (3232, 17280)]

def row868 : Integer.Sparse (Fin 3237) := [(0, -113), (32, 20), (160, -480), (225, -160), (255, -80), (256, -240), (261, -75), (274, 240), (1686, 4320), (1687, 4320), (1691, 4320), (1697, 4320), (1797, 4320), (1798, 4320), (1838, 4320), (1897, 4320), (1941, 4320), (2337, 4320), (2340, 4320), (2345, 4320), (2497, 4320), (2523, 4320), (2533, 4320), (2535, 4320), (2725, 4320), (2729, 4320), (2739, 4320), (2740, 4320), (2745, 4320), (2746, 4320), (2748, 4320), (2749, 4320), (2772, 4320), (2777, 4320)]

def row869 : Integer.Sparse (Fin 3237) := [(2098, 1), (2747, 1), (2772, 1), (2777, 1), (2783, 1), (2793, 1), (2839, -1)]

def row870 : Integer.Sparse (Fin 3237) := [(1869, 1), (2184, 1), (2709, 1), (2742, 1), (2747, 1), (2749, 1), (2839, -1)]

def row871 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 5), (261, -10), (2610, -720), (2622, -720), (2643, -720), (2668, -720), (2669, -720), (2699, -1440), (2701, -720), (2703, -1440), (2723, -1440), (2729, -720), (2742, -720), (2783, -720), (2786, -720), (2803, -720), (3045, 2880), (3046, 2880), (3052, 2880), (3053, 2880), (3055, 2880), (3140, 2880), (3144, 2880), (3147, 2880), (3178, 2880), (3206, 2880), (3215, 2880), (3217, 2880), (3218, 5760), (3219, 2880), (3220, 2880), (3225, 2880), (3230, 2880), (3231, 2880), (3232, 2880)]

def row872 : Integer.Sparse (Fin 3237) := [(0, -2472), (3, -240), (32, -1560), (159, 2880), (160, -7680), (162, -960), (218, 2880), (222, 2880), (224, 5760), (225, -3840), (256, -2880), (260, -1440), (261, 4800), (274, 2880), (1447, 51840), (1448, 51840), (1455, 51840), (1463, 51840), (1599, 51840), (1850, 51840), (1857, 51840), (1868, 51840), (1939, 51840), (2638, 51840), (2644, 51840), (2678, 51840), (2680, 51840), (2695, 51840), (2701, 51840), (2703, 51840), (2709, 51840), (2728, 51840), (2732, 51840), (2734, 51840), (2742, 51840), (2746, 51840), (2748, 51840)]

def row873 : Integer.Sparse (Fin 3237) := [(0, -393), (3, -60), (32, -165), (160, -1680), (162, -240), (218, 720), (219, 720), (225, -960), (252, 720), (255, -240), (256, -720), (260, 180), (261, 480), (1459, 12960), (1460, 12960), (1463, 12960), (1469, 12960), (1615, 12960), (2463, 12960), (2468, 12960), (2495, 12960), (2525, 12960), (2641, 12960), (2644, 12960), (2661, 12960), (2668, 12960), (2669, 12960), (2680, 12960), (2683, 12960), (2703, 12960), (2711, 12960), (2723, 12960), (2734, 12960), (2739, 12960), (2743, 12960), (2746, 12960), (2747, 12960), (2783, 12960)]

def row874 : Integer.Sparse (Fin 3237) := [(2033, 1), (2610, 1), (2634, 1), (2644, 1), (2723, 1), (2784, 1), (2840, -1)]

def row875 : Integer.Sparse (Fin 3237) := [(2226, 1), (2608, 1), (2610, 1), (2622, 1), (2699, 1), (2784, 1), (2840, -1)]

def row876 : Integer.Sparse (Fin 3237) := [(2148, 1), (2641, 1), (2643, 1), (2644, 1), (2729, 1), (2784, 1), (2840, -1)]

def row877 : Integer.Sparse (Fin 3237) := [(0, -824), (3, -80), (32, -420), (159, 960), (160, -960), (162, -320), (225, -640), (256, -320), (261, 1140), (1763, 17280), (1764, 17280), (1771, 17280), (1778, 17280), (1844, 17280), (1845, 17280), (1869, 17280), (1902, 17280), (1974, 17280), (2521, 17280), (2525, 17280), (2527, 17280), (2530, 17280), (2613, 17280), (2616, 17280), (2724, 17280), (2727, 17280), (2728, 17280), (2736, 17280), (2737, 17280), (2744, 17280), (2747, 17280), (2750, 17280)]

def row878 : Integer.Sparse (Fin 3237) := [(0, -256), (32, -170), (160, -160), (252, -480), (255, -160), (261, 110), (2040, 8640), (2041, 8640), (2042, 8640), (2051, 8640), (2186, 8640), (2363, 8640), (2364, 8640), (2365, 8640), (2374, 8640), (2417, 8640), (2448, 8640), (2533, 8640), (2539, 8640), (2652, 8640), (2659, 8640), (2665, 8640), (2670, 8640), (2699, 8640), (2743, 8640), (2780, 8640), (2783, 8640), (2784, 8640), (2787, 8640), (2789, 8640), (2795, 8640)]

def row879 : Integer.Sparse (Fin 3237) := [(2048, 1), (2621, 1), (2748, 1), (2786, 1), (2787, 1), (2840, -1)]

def row880 : Integer.Sparse (Fin 3237) := [(2035, 1), (2037, 1), (2039, 1), (2048, 1), (2152, 1), (2748, 1), (2840, -1)]

def row881 : Integer.Sparse (Fin 3237) := [(0, -87), (225, 80), (256, -80), (261, 15), (1305, 2160), (1306, 2160), (1308, 2160), (1330, 2160), (1611, 2160), (2023, 2160), (2024, 2160), (2047, 2160), (2177, 2160), (2351, 2160), (2352, 2160), (2370, 2160), (2519, 2160), (2583, 2160), (2587, 2160), (2673, 2160), (2677, 2160), (2694, 2160), (2697, 2160), (2699, 6480), (2705, 2160), (2769, 2160), (2794, 2160), (2797, 2160)]

def row882 : Integer.Sparse (Fin 3237) := [(0, 114), (32, 55), (160, 80), (256, 80), (261, -95), (1760, -4320), (1784, -4320), (2446, -4320), (2447, -4320), (2610, -4320), (2622, -4320), (2633, -4320), (2643, -4320), (2668, -4320), (2669, -4320), (2677, -4320), (2689, -4320), (2690, -4320), (2693, -4320), (2698, -4320), (2699, -4320), (2701, -4320), (2703, -4320), (2704, -17280), (2764, -4320), (2803, -4320), (3048, 17280), (3049, 17280), (3052, 17280), (3055, 17280), (3065, 17280), (3108, 17280), (3175, 17280), (3206, 17280), (3220, 17280), (3221, 17280), (3226, 17280), (3230, 17280), (3231, 17280), (3232, 34560)]

def row883 : Integer.Sparse (Fin 3237) := [(0, -154), (32, -105), (160, -480), (162, -240), (225, -160), (256, -160), (261, 165), (1598, 4320), (1599, 4320), (1601, 4320), (1607, 4320), (1615, 4320), (2433, 4320), (2446, 4320), (2447, 4320), (2497, 4320), (2661, 4320), (2668, 4320), (2669, 4320), (2689, 4320), (2690, 4320), (2693, 4320), (2695, 4320), (2696, 4320), (2701, 4320), (2704, 4320), (2719, 4320), (2728, 4320), (2746, 4320), (2747, 4320), (2748, 4320)]

def row884 : Integer.Sparse (Fin 3237) := [(0, 30), (32, 13), (160, -16), (256, -16), (261, -29), (1782, -864), (2160, -864), (2439, -864), (2574, -864), (2621, -864), (2665, -864), (2676, -864), (2688, -864), (2694, -864), (2699, -864), (2702, -864), (2703, -864), (2704, -1728), (2764, -864), (2765, -864), (2766, -864), (2769, -864), (3112, 3456), (3113, 3456), (3114, 3456), (3115, 6912), (3119, 3456), (3180, 3456), (3191, 3456), (3192, 3456), (3194, 3456), (3197, 3456), (3209, 3456), (3210, 3456), (3211, 3456), (3226, 3456), (3229, 3456), (3232, 3456)]

def row885 : Integer.Sparse (Fin 3237) := [(0, -30), (32, -13), (160, 16), (256, 16), (261, 29), (2133, 864), (2134, 864), (2135, 864), (2157, 864), (2186, 864), (2431, 864), (2434, 864), (2439, 864), (2440, 864), (2448, 1728), (2492, 864), (2574, 864), (2659, 864), (2662, 864), (2665, 864), (2670, 864), (2688, 864), (2694, 864), (2699, 864), (2704, 864), (2718, 864), (2784, 864), (2789, 864)]

def row886 : Integer.Sparse (Fin 3237) := [(0, 8), (32, -5), (261, 15), (2607, -720), (2664, -720), (2693, -360), (2698, -360), (2726, -360), (2741, -360), (2749, -720), (2782, -1440), (2783, -720), (2786, -720), (2794, -360), (2802, -360), (3102, 1440), (3105, 1440), (3107, 2880), (3139, 1440), (3142, 2880), (3168, 1440), (3190, 1440), (3204, 1440), (3205, 2880), (3225, 2880), (3228, 1440), (3235, 2880), (3236, 2880)]

def row887 : Integer.Sparse (Fin 3237) := [(0, -1140), (3, -720), (32, 2670), (66, 960), (71, 960), (159, -2880), (160, 6720), (162, 480), (222, -2880), (225, 1920), (256, 4800), (260, 2880), (261, -7110), (273, -2880), (274, -5760), (1742, 25920), (1746, 25920), (1751, 51840), (1846, 25920), (1852, 51840), (1915, 25920), (1958, 25920), (2602, 25920), (2605, 51840), (2724, 25920), (2739, 51840), (2741, 25920), (2749, 25920), (2777, 51840), (2792, 51840)]

def row888 : Integer.Sparse (Fin 3237) := [(0, -103), (32, 125), (160, 560), (225, 160), (255, 160), (256, 480), (261, -560), (2413, 4320), (2415, 8640), (2444, 4320), (2455, 4320), (2459, 4320), (2487, 8640), (2535, 4320), (2650, 8640), (2664, 8640), (2666, 4320), (2698, 4320), (2740, 4320), (2776, 8640), (2781, 8640), (2782, 8640), (2786, 8640), (2792, 8640)]

def row889 : Integer.Sparse (Fin 3237) := [(2114, 1), (2602, 1), (2607, 2), (2693, 1), (2839, -1)]

def row890 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 5), (261, -10), (2606, -360), (2620, -360), (2657, -360), (2658, -360), (2681, -360), (2692, -360), (2693, -720), (2698, -720), (2723, -1440), (2729, -720), (2742, -720), (2783, -720), (2786, -720), (2803, -720), (3140, 2880), (3143, 1440), (3146, 1440), (3177, 1440), (3206, 2880), (3219, 2880), (3220, 2880), (3222, 2880), (3228, 1440), (3232, 2880)]

def row891 : Integer.Sparse (Fin 3237) := [(0, -615), (3, 120), (4, -15), (32, -195), (66, 240), (68, 240), (160, 1680), (162, 240), (218, -720), (219, -720), (225, 480), (252, -1440), (255, 480), (256, 480), (260, -180), (261, 555), (2463, 25920), (2467, 12960), (2494, 12960), (2524, 12960), (2657, 12960), (2658, 12960), (2661, 25920), (2680, 25920), (2683, 25920), (2693, 12960), (2723, 25920), (2735, 12960), (2748, 25920), (2778, 12960), (2780, 12960), (2783, 25920)]

def row892 : Integer.Sparse (Fin 3237) := [(0, -1992), (3, -240), (32, -930), (66, 480), (71, 480), (159, -2880), (160, 1920), (162, 480), (218, -1440), (222, -1440), (224, -2880), (225, 960), (256, 960), (260, 720), (261, 1230), (1850, 51840), (1854, 25920), (1867, 25920), (1938, 25920), (2678, 51840), (2680, 51840), (2692, 25920), (2693, 25920), (2695, 51840), (2724, 25920), (2735, 25920), (2742, 51840), (2747, 51840), (2778, 25920)]

def row893 : Integer.Sparse (Fin 3237) := [(2606, 1), (2608, 2), (2620, 1), (2698, 1), (2840, -1)]

def row894 : Integer.Sparse (Fin 3237) := [(0, -184), (3, 40), (4, -10), (32, 500), (159, -480), (160, 2720), (162, 320), (165, 160), (225, 1120), (255, 160), (256, 1760), (261, -1570), (274, -960), (1729, 8640), (1732, 8640), (1736, 8640), (1765, 8640), (1793, 8640), (1797, 8640), (1820, 8640), (1889, 8640), (1941, 8640), (2523, 8640), (2524, 8640), (2526, 8640), (2529, 8640), (2599, 8640), (2614, 8640), (2719, 8640), (2725, 8640), (2726, 8640), (2745, 8640), (2746, 17280), (2748, 8640), (2749, 8640)]

def row895 : Integer.Sparse (Fin 3237) := [(2109, 1), (2744, 1), (2746, 2), (2767, 1), (2775, 1), (2839, -1)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row896 : Integer.Sparse (Fin 3237) := [(0, 11), (32, 5), (261, -10), (2633, -1440), (2677, -1440), (2689, -1440), (2690, -1440), (2699, -1440), (2703, -1440), (2717, -1440), (2722, -1440), (2803, -720), (3044, 2880), (3045, 5760), (3048, 5760), (3215, 5760), (3216, 5760), (3217, 5760), (3224, 5760), (3225, 5760), (3226, 5760), (3232, 5760)]

def row897 : Integer.Sparse (Fin 3237) := [(0, -171), (4, -5), (32, 5), (66, 160), (68, 160), (159, -240), (160, 1280), (162, 240), (165, 80), (218, -480), (219, -240), (222, -240), (224, -480), (225, 480), (252, -240), (255, 240), (256, 400), (260, 60), (261, 5), (1446, 4320), (1447, 4320), (1450, 4320), (1459, 4320), (1598, 4320), (2637, 4320), (2638, 4320), (2641, 4320), (2689, 4320), (2690, 4320), (2703, 4320), (2708, 4320), (2709, 4320), (2711, 4320), (2713, 4320), (2717, 4320), (2719, 4320), (2732, 4320), (2736, 4320), (2738, 4320), (2739, 4320), (2747, 4320), (2748, 4320)]

def row898 : Integer.Sparse (Fin 3237) := [(0, 763), (32, -120), (256, 80), (261, 645), (1753, -4320), (1755, -4320), (1761, -4320), (1782, -4320), (1810, -4320), (1815, -4320), (1934, -4320), (2437, -4320), (2438, -4320), (2439, -4320), (2450, -4320), (2480, -4320), (2481, -4320), (2501, -4320), (2557, -4320), (2575, -4320), (2607, -4320), (2611, -4320), (2621, -4320), (2664, -4320), (2665, -4320), (2671, -4320), (2764, -4320), (2775, -4320), (2779, -4320), (2783, -4320), (2786, -4320), (2794, -4320), (2799, -4320), (2801, -4320), (2802, -8640), (2803, -8640)]

def row899 : Integer.Sparse (Fin 3237) := [(0, -27), (32, 5), (261, -20), (1753, 180), (1755, 180), (1761, 180), (1782, 180), (1810, 180), (1815, 180), (1934, 180), (2607, 180), (2611, 180), (2621, 180), (2775, 180), (2783, 180)]

def row900 : Integer.Sparse (Fin 3237) := [(0, 81), (32, 40), (160, 80), (256, 80), (261, -65), (2693, -4320), (2698, -4320), (2699, -4320), (2703, -4320), (2717, -4320), (2722, -4320), (2723, -8640), (2729, -4320), (2742, -4320), (2764, -4320), (2783, -4320), (2786, -4320), (2803, -2160), (3231, 8640), (3232, 17280)]

def row901 : Integer.Sparse (Fin 3237) := [(0, 79), (32, -55), (160, -80), (225, -40), (256, -80), (261, 230), (1753, -4320), (2177, -2160), (2437, -4320), (2573, -2160), (2607, -4320), (2664, -4320), (2682, -4320), (2694, -2160), (2697, -4320), (2702, -2160), (2762, -2160), (2763, -2160), (2794, -2160), (2802, -2160), (3103, 8640), (3105, 17280), (3108, 17280), (3204, 8640), (3206, 17280), (3229, 17280), (3236, 17280)]

def row902 : Integer.Sparse (Fin 3237) := [(0, -79), (32, 55), (160, 80), (225, 40), (256, 80), (261, -230), (2433, 4320), (2436, 2160), (2437, 4320), (2444, 4320), (2573, 2160), (2661, 4320), (2664, 4320), (2666, 2160), (2697, 4320), (2702, 2160), (2725, 4320), (2792, 4320)]

def row903 : Integer.Sparse (Fin 3237) := [(0, 114), (32, 55), (160, 80), (256, 80), (261, -95), (1752, -2160), (1780, -2160), (2429, -2160), (2430, -2160), (2606, -2160), (2620, -2160), (2657, -2160), (2658, -2160), (2681, -2160), (2692, -2160), (2693, -2160), (2694, -4320), (2698, -2160), (2699, -4320), (2702, -4320), (2703, -4320), (2764, -4320), (2803, -4320), (3108, 17280), (3206, 17280), (3220, 17280), (3221, 17280), (3228, 8640)]

def row904 : Integer.Sparse (Fin 3237) := [(0, -116), (32, -25), (160, 400), (162, 160), (225, 240), (256, 80), (261, -25), (2429, 2160), (2430, 2160), (2433, 4320), (2657, 2160), (2658, 2160), (2661, 4320), (2692, 2160), (2694, 2160), (2695, 4320), (2696, 4320), (2703, 4320), (2724, 2160)]

def row905 : Integer.Sparse (Fin 3237) := [(0, 41), (32, -5), (160, 80), (225, 40), (256, 80), (261, 70), (1934, -2160), (2097, -2160), (2501, -2160), (2556, -2160), (2682, -2160), (2685, -2160), (2697, -2160), (2705, -2160), (2717, -2160), (2722, -2160), (2726, -2160), (2729, -2160), (2741, -2160), (2742, -2160), (2749, -4320), (2763, -2160), (2793, -8640), (2794, -2160), (3125, 8640), (3126, 8640), (3127, 8640), (3142, 8640), (3145, 8640), (3148, 8640), (3159, 8640), (3160, 8640), (3166, 8640), (3175, 8640), (3194, 8640), (3223, 8640), (3225, 8640), (3229, 8640), (3232, 8640), (3236, 8640)]

def row906 : Integer.Sparse (Fin 3237) := [(0, -194), (32, 60), (160, -640), (225, -160), (255, -160), (256, -320), (261, -290), (1893, 8640), (1894, 8640), (1897, 8640), (1905, 8640), (1967, 8640), (2477, 8640), (2482, 8640), (2487, 8640), (2497, 8640), (2499, 8640), (2501, 8640), (2533, 8640), (2556, 8640), (2697, 8640), (2705, 8640), (2721, 8640), (2722, 8640), (2725, 8640), (2726, 8640), (2729, 8640), (2739, 8640), (2748, 8640), (2749, 8640), (2792, 8640), (2793, 8640)]

def row907 : Integer.Sparse (Fin 3237) := [(1858, 1), (2189, 1), (2685, 1), (2707, 1), (2742, 2), (2839, -1)]

def row908 : Integer.Sparse (Fin 3237) := [(0, 1347), (3, 60), (32, 135), (66, 240), (160, 720), (222, -720), (225, 240), (260, -180), (261, -1680), (1415, -12960), (1416, -12960), (1417, -12960), (1424, -12960), (1438, -12960), (1440, -12960), (1443, -12960), (1468, -12960), (1569, -12960), (1608, -12960), (1750, -12960), (1760, -12960), (1777, -12960), (1969, -12960), (2414, -12960), (2418, -12960), (2446, -12960), (2537, -12960), (2604, -12960), (2610, -12960), (2618, -12960), (2619, -25920), (2622, -12960), (2635, -12960), (2649, -12960), (2651, -12960), (2668, -12960), (2669, -12960), (2677, -12960), (2682, -12960), (2690, -12960), (2697, -12960), (2715, -12960), (2726, -12960), (2727, -25920), (2729, -12960), (2741, -12960), (2742, -12960), (2753, -12960), (2764, -12960), (2765, -12960), (2766, -12960), (2768, -12960), (2769, -12960), (2793, -25920)]

def row909 : Integer.Sparse (Fin 3237) := [(0, -810), (3, -60), (32, -45), (66, -240), (160, -720), (222, 720), (225, -240), (256, -240), (260, 180), (261, 1185), (1438, 12960), (1440, 12960), (1443, 12960), (1468, 12960), (1569, 12960), (1750, 12960), (1760, 12960), (1777, 12960), (1969, 12960), (2604, 12960), (2610, 12960), (2619, 12960), (2635, 12960), (2651, 12960), (2669, 12960), (2682, 12960), (2690, 12960), (2727, 12960), (2741, 12960), (2742, 12960), (2765, 12960), (2766, 12960), (2793, 12960)]

def row910 : Integer.Sparse (Fin 3237) := [(0, 66), (32, 25), (160, -160), (225, -80), (256, -80), (261, -5), (1837, -2160), (1979, -2160), (2519, -2160), (2538, -2160), (2643, -2160), (2681, -2160), (2692, -2160), (2701, -2160), (2717, -2160), (2722, -2160), (2723, -8640), (2727, -4320), (2729, -2160), (2742, -2160), (2766, -2160), (2769, -2160), (2783, -2160), (2786, -2160), (2803, -2160), (3134, 8640), (3136, 8640), (3137, 8640), (3177, 8640), (3178, 8640), (3181, 8640), (3197, 8640), (3217, 8640), (3218, 8640), (3222, 8640), (3226, 8640), (3229, 8640), (3230, 8640), (3232, 8640)]

def row911 : Integer.Sparse (Fin 3237) := [(0, -390), (32, -230), (160, 160), (225, 160), (256, 160), (261, 200), (274, 480), (1938, 8640), (1939, 8640), (1942, 8640), (1944, 8640), (1973, 8640), (2513, 8640), (2519, 8640), (2520, 8640), (2538, 8640), (2692, 8640), (2701, 8640), (2717, 8640), (2723, 8640), (2727, 8640), (2732, 8640), (2734, 8640), (2735, 8640), (2737, 8640), (2738, 8640), (2742, 8640), (2743, 8640), (2747, 8640)]

def row912 : Integer.Sparse (Fin 3237) := [(0, 4974), (3, -120), (4, 30), (32, -660), (71, -960), (160, -960), (256, -1920), (260, 360), (261, 6240), (273, 1440), (1727, -25920), (1728, -51840), (1737, -51840), (1753, -51840), (1934, -51840), (2405, -25920), (2406, -51840), (2408, -51840), (2437, -51840), (2501, -51840), (2597, -25920), (2601, -51840), (2607, -51840), (2646, -25920), (2647, -51840), (2664, -51840), (2717, -51840), (2722, -51840), (2774, -51840), (2783, -51840), (2786, -51840), (2791, -103680), (2801, -25920), (2802, -51840), (2803, -51840)]

def row913 : Integer.Sparse (Fin 3237) := [(0, -3318), (3, 120), (4, -30), (32, 660), (71, 960), (160, 960), (256, 1920), (260, -360), (261, -4440), (273, -1440), (1727, 25920), (1728, 51840), (1737, 51840), (1753, 51840), (1934, 51840), (2597, 25920), (2601, 51840), (2607, 51840), (2717, 51840), (2774, 25920), (2783, 51840), (2791, 51840)]

def row914 : Integer.Sparse (Fin 3237) := [(0, 114), (32, 55), (160, 80), (256, 80), (261, -95), (2676, -4320), (2677, -4320), (2688, -4320), (2690, -4320), (2716, -4320), (2717, -8640), (2722, -8640), (2764, -4320), (2783, -4320), (2786, -4320), (2803, -4320), (3224, 8640), (3225, 17280), (3226, 17280), (3229, 17280), (3231, 17280)]

def row915 : Integer.Sparse (Fin 3237) := [(0, -141), (32, -55), (160, 480), (225, 160), (252, -120), (255, 160), (256, 160), (261, 10), (2688, 4320), (2690, 4320), (2717, 4320), (2736, 2160), (2738, 4320), (2739, 4320), (2746, 4320), (2783, 4320), (2789, 4320)]

def row916 : Integer.Sparse (Fin 3237) := [(0, 40), (32, -30), (225, 40), (256, -80), (261, 210), (1810, -2160), (1934, -2160), (2081, -2160), (2480, -2160), (2501, -2160), (2555, -2160), (2635, -2160), (2674, -2160), (2691, -2160), (2715, -2160), (2717, -4320), (2722, -4320), (2726, -2160), (2729, -2160), (2741, -2160), (2742, -2160), (2763, -2160), (2791, -4320), (2802, -2160), (3122, 8640), (3123, 8640), (3125, 8640), (3129, 8640), (3170, 8640), (3214, 8640), (3215, 8640), (3223, 8640), (3225, 8640), (3228, 8640), (3229, 8640), (3236, 8640)]

def row917 : Integer.Sparse (Fin 3237) := [(0, -40), (32, 30), (225, -40), (256, 80), (261, -210), (2476, 2160), (2477, 2160), (2479, 2160), (2480, 2160), (2496, 2160), (2501, 2160), (2517, 2160), (2555, 2160), (2691, 2160), (2711, 2160), (2714, 2160), (2715, 2160), (2721, 2160), (2722, 4320), (2725, 2160), (2729, 2160), (2739, 2160), (2740, 2160), (2741, 2160), (2791, 2160), (2792, 2160)]

def row919 : Integer.Sparse (Fin 3237) := [(0, -993), (3, 60), (4, -15), (32, 360), (66, 240), (71, 240), (160, 1440), (222, -720), (225, 480), (256, 1440), (260, -180), (261, -1200), (1359, 12960), (1361, 12960), (1370, 12960), (1389, 12960), (1549, 12960), (1728, 12960), (1735, 12960), (1752, 12960), (1933, 12960), (2597, 12960), (2600, 12960), (2601, 12960), (2606, 12960), (2607, 12960), (2647, 12960), (2658, 12960), (2716, 12960), (2717, 12960), (2722, 12960), (2723, 12960), (2762, 12960), (2763, 12960), (2791, 12960)]

end MUB6.Certificate.MixedData

end OAI
end


