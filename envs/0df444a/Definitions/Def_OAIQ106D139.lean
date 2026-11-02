-- Prove2me | Definitions.Def_OAIQ106D139
-- name    : OAIQ106D139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:31:08.338823+00:00
-- url     : https://prove2.me/theorems/5796443e-2414-402c-8af9-c1e88c5c7890
-- title:
--   Definitions bundle OAIQ106D139 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2430 declarations of OpenAI's Lean: 2430 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.boundaryRow88`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow89`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow90`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow91`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow92`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow93`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow94`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow95`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow96`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow97`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow98`, `OAI.MUB6.Certificate.PairSemantics.boundaryRow99`, `OAI.MUB6.Certificate.PairSemantics.value1006`, `OAI.MUB6.Certificate.PairSemantics.value1007`, `OAI.MUB6.Certificate.PairSemantics.value1008`, `OAI.MUB6.Certificate.PairSemantics.value1009`, `OAI.MUB6.Certificate.PairSemantics.value1010`, `OAI.MUB6.Certificate.PairSemantics.value1011`, `OAI.MUB6.Certificate.PairSemantics.value1012`, `OAI.MUB6.Certificate.PairSemantics.value1013`, `OAI.MUB6.Certificate.PairSemantics.value1014`, `OAI.MUB6.Certificate.PairSemantics.value1015`, `OAI.MUB6.Certificate.PairSemantics.value1016`, `OAI.MUB6.Certificate.PairSemantics.value1017`, `OAI.MUB6.Certificate.PairSemantics.value1018`, `OAI.MUB6.Certificate.PairSemantics.value1019`, `OAI.MUB6.Certificate.PairSemantics.value1020`, `OAI.MUB6.Certificate.PairSemantics.value1021`, `OAI.MUB6.Certificate.PairSemantics.value1022`, `OAI.MUB6.Certificate.PairSemantics.value1023`, `OAI.MUB6.Certificate.PairSemantics.value1024`, `OAI.MUB6.Certificate.PairSemantics.value1025`, `OAI.MUB6.Certificate.PairSemantics.value1026`, `OAI.MUB6.Certificate.PairSemantics.value1027`, `OAI.MUB6.Certificate.PairSemantics.value1028`, `OAI.MUB6.Certificate.PairSemantics.value1029`, `OAI.MUB6.Certificate.PairSemantics.value1030`, `OAI.MUB6.Certificate.PairSemantics.value1031`, `OAI.MUB6.Certificate.PairSemantics.value1032`, `OAI.MUB6.Certificate.PairSemantics.value1033` and 2390 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Boundary5`, `MutuallyUnbiased_PairSemantics_Values0`, `MutuallyUnbiased_PairSemantics_Values1`, `MutuallyUnbiased_PairSemantics_Values15`, `MutuallyUnbiased_PairSemantics_Values16`, `MutuallyUnbiased_PairSemantics_Values17`, `MutuallyUnbiased_PairSemantics_Values18`, `MutuallyUnbiased_PairSemantics_Values19`, `MutuallyUnbiased_PairSemantics_Values2`, `MutuallyUnbiased_PairSemantics_Values20`, `MutuallyUnbiased_PairSemantics_Values21`, `MutuallyUnbiased_PairSemantics_Values22`, `MutuallyUnbiased_PairSemantics_Values23`, `MutuallyUnbiased_PairSemantics_Values24`, `MutuallyUnbiased_PairSemantics_Values25`, `MutuallyUnbiased_PairSemantics_Values26`, `MutuallyUnbiased_PairSemantics_Values27`, `MutuallyUnbiased_PairSemantics_Values28`, `MutuallyUnbiased_PairSemantics_Values29`, `MutuallyUnbiased_PairSemantics_Values3`, `MutuallyUnbiased_PairSemantics_Values30`, `MutuallyUnbiased_PairSemantics_Values31`, `MutuallyUnbiased_PairSemantics_Values32`, `MutuallyUnbiased_PairSemantics_Values33`, `MutuallyUnbiased_PairSemantics_Values34`, `MutuallyUnbiased_PairSemantics_Values35`, `MutuallyUnbiased_PairSemantics_Values36`, `MutuallyUnbiased_PairSemantics_Values37`, `MutuallyUnbiased_PairSemantics_Values38`, `MutuallyUnbiased_PairSemantics_Values39`, `MutuallyUnbiased_PairSemantics_Values4`, `MutuallyUnbiased_PairSemantics_Values40`, `MutuallyUnbiased_PairSemantics_Values41`, `MutuallyUnbiased_PairSemantics_Values42`, `MutuallyUnbiased_PairSemantics_Values43`, `MutuallyUnbiased_PairSemantics_Values44`, `MutuallyUnbiased_PairSemantics_Values45`, `MutuallyUnbiased_PairSemantics_Values46`, `MutuallyUnbiased_PairSemantics_Values47`, `MutuallyUnbiased_PairSemantics_Values48`, `MutuallyUnbiased_PairSemantics_Values49`, `MutuallyUnbiased_PairSemantics_Values5`.
--
--   **Imports.** It imports the bundles `OAIQ106D000` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound11`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1294`, `OAI.MUB6.Certificate.PairSemantics.sound1323`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189` and `OAI.MUB6.Certificate.PairSemantics.sound3191`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1162`, `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1164`, `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound1265`, `OAI.MUB6.Certificate.MixedSemantics.sound1266`, `OAI.MUB6.Certificate.MixedSemantics.sound1267`, `OAI.MUB6.Certificate.MixedSemantics.sound1271`, `OAI.MUB6.Certificate.MixedSemantics.sound1298`, `OAI.MUB6.Certificate.MixedSemantics.sound1299`, `OAI.MUB6.Certificate.MixedSemantics.sound1301`, `OAI.MUB6.Certificate.MixedSemantics.sound1339`, `OAI.MUB6.Certificate.MixedSemantics.sound1340`, `OAI.MUB6.Certificate.MixedSemantics.sound1341`, `OAI.MUB6.Certificate.MixedSemantics.sound1342`, `OAI.MUB6.Certificate.MixedSemantics.sound1343`, `OAI.MUB6.Certificate.MixedSemantics.sound1344`, `OAI.MUB6.Certificate.MixedSemantics.sound1346`, `OAI.MUB6.Certificate.MixedSemantics.sound1395`, `OAI.MUB6.Certificate.MixedSemantics.sound1396`, `OAI.MUB6.Certificate.MixedSemantics.sound1397`, `OAI.MUB6.Certificate.MixedSemantics.sound1399`, `OAI.MUB6.Certificate.MixedSemantics.sound1401`, `OAI.MUB6.Certificate.MixedSemantics.sound1409`, `OAI.MUB6.Certificate.MixedSemantics.sound1410`, `OAI.MUB6.Certificate.MixedSemantics.sound1411`, `OAI.MUB6.Certificate.MixedSemantics.sound1412`, `OAI.MUB6.Certificate.MixedSemantics.sound1413`, `OAI.MUB6.Certificate.MixedSemantics.sound1414`, `OAI.MUB6.Certificate.MixedSemantics.sound1416`, `OAI.MUB6.Certificate.MixedSemantics.sound1417`, `OAI.MUB6.Certificate.MixedSemantics.sound1427`, `OAI.MUB6.Certificate.MixedSemantics.sound1441`, `OAI.MUB6.Certificate.MixedSemantics.sound1443`, `OAI.MUB6.Certificate.MixedSemantics.sound1451`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sound1478`, `OAI.MUB6.Certificate.MixedSemantics.sound1479`, `OAI.MUB6.Certificate.MixedSemantics.sound1480`, `OAI.MUB6.Certificate.MixedSemantics.sound171`, `OAI.MUB6.Certificate.MixedSemantics.sound174`, `OAI.MUB6.Certificate.MixedSemantics.sound206`, `OAI.MUB6.Certificate.MixedSemantics.sound207`, `OAI.MUB6.Certificate.MixedSemantics.sound2357`, `OAI.MUB6.Certificate.MixedSemantics.sound2358`, `OAI.MUB6.Certificate.MixedSemantics.sound2359`, `OAI.MUB6.Certificate.MixedSemantics.sound2527`, `OAI.MUB6.Certificate.MixedSemantics.sound2530`, `OAI.MUB6.Certificate.MixedSemantics.sound2531`, `OAI.MUB6.Certificate.MixedSemantics.sound2532`, `OAI.MUB6.Certificate.MixedSemantics.sound2570`, `OAI.MUB6.Certificate.MixedSemantics.sound2572`, `OAI.MUB6.Certificate.MixedSemantics.sound2574`, `OAI.MUB6.Certificate.MixedSemantics.sound2576`, `OAI.MUB6.Certificate.MixedSemantics.sound2593`, `OAI.MUB6.Certificate.MixedSemantics.sound2594`, `OAI.MUB6.Certificate.MixedSemantics.sound2595`, `OAI.MUB6.Certificate.MixedSemantics.sound2596`, `OAI.MUB6.Certificate.MixedSemantics.sound2598`, `OAI.MUB6.Certificate.MixedSemantics.sound2599`, `OAI.MUB6.Certificate.MixedSemantics.sound2601`, `OAI.MUB6.Certificate.MixedSemantics.sound2636`, `OAI.MUB6.Certificate.MixedSemantics.sound2637`, `OAI.MUB6.Certificate.MixedSemantics.sound2638`, `OAI.MUB6.Certificate.MixedSemantics.sound2640`, `OAI.MUB6.Certificate.MixedSemantics.sound2753`, `OAI.MUB6.Certificate.MixedSemantics.sound2766`, `OAI.MUB6.Certificate.MixedSemantics.sound2828`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound293`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound294`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSemantics.sound2988`, `OAI.MUB6.Certificate.MixedSemantics.sound2990`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSemantics.sound3082`, `OAI.MUB6.Certificate.MixedSemantics.sound3087`, `OAI.MUB6.Certificate.MixedSemantics.sound3088`, `OAI.MUB6.Certificate.MixedSemantics.sound3089`, `OAI.MUB6.Certificate.MixedSemantics.sound3090`, `OAI.MUB6.Certificate.MixedSemantics.sound3093`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound3120`, `OAI.MUB6.Certificate.MixedSemantics.sound3143`, `OAI.MUB6.Certificate.MixedSemantics.sound3144`, `OAI.MUB6.Certificate.MixedSemantics.sound3178`, `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound370`, `OAI.MUB6.Certificate.MixedSemantics.sound371`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSemantics.sound3727`, `OAI.MUB6.Certificate.MixedSemantics.sound3734`, `OAI.MUB6.Certificate.MixedSemantics.sound3735`, `OAI.MUB6.Certificate.MixedSemantics.sound3736`, `OAI.MUB6.Certificate.MixedSemantics.sound3737`, `OAI.MUB6.Certificate.MixedSemantics.sound3738`, `OAI.MUB6.Certificate.MixedSemantics.sound3739`, `OAI.MUB6.Certificate.MixedSemantics.sound3818`, `OAI.MUB6.Certificate.MixedSemantics.sound3821`, `OAI.MUB6.Certificate.MixedSemantics.sound3822`, `OAI.MUB6.Certificate.MixedSemantics.sound3823`, `OAI.MUB6.Certificate.MixedSemantics.sound3824`, `OAI.MUB6.Certificate.MixedSemantics.sound3829`, `OAI.MUB6.Certificate.MixedSemantics.sound3831`, `OAI.MUB6.Certificate.MixedSemantics.sound3847`, `OAI.MUB6.Certificate.MixedSemantics.sound3851`, `OAI.MUB6.Certificate.MixedSemantics.sound3852`, `OAI.MUB6.Certificate.MixedSemantics.sound3853`, `OAI.MUB6.Certificate.MixedSemantics.sound3855`, `OAI.MUB6.Certificate.MixedSemantics.sound3856`, `OAI.MUB6.Certificate.MixedSemantics.sound3858`, `OAI.MUB6.Certificate.MixedSemantics.sound3882`, `OAI.MUB6.Certificate.MixedSemantics.sound3883`, `OAI.MUB6.Certificate.MixedSemantics.sound3887`, `OAI.MUB6.Certificate.MixedSemantics.sound3888`, `OAI.MUB6.Certificate.MixedSemantics.sound3925`, `OAI.MUB6.Certificate.MixedSemantics.sound3931`, `OAI.MUB6.Certificate.MixedSemantics.sound3933`, `OAI.MUB6.Certificate.MixedSemantics.sound3936`, `OAI.MUB6.Certificate.MixedSemantics.sound3937`, `OAI.MUB6.Certificate.MixedSemantics.sound3965`, `OAI.MUB6.Certificate.MixedSemantics.sound3966`, `OAI.MUB6.Certificate.MixedSemantics.sound3967`, `OAI.MUB6.Certificate.MixedSemantics.sound3977`, `OAI.MUB6.Certificate.MixedSemantics.sound3980`, `OAI.MUB6.Certificate.MixedSemantics.sound3982`, `OAI.MUB6.Certificate.MixedSemantics.sound3984`, `OAI.MUB6.Certificate.MixedSemantics.sound3987`, `OAI.MUB6.Certificate.MixedSemantics.sound3992`, `OAI.MUB6.Certificate.MixedSemantics.sound3993`, `OAI.MUB6.Certificate.MixedSemantics.sound3994`, `OAI.MUB6.Certificate.MixedSemantics.sound3997`, `OAI.MUB6.Certificate.MixedSemantics.sound3998`, `OAI.MUB6.Certificate.MixedSemantics.sound4002`, `OAI.MUB6.Certificate.MixedSemantics.sound4003`, `OAI.MUB6.Certificate.MixedSemantics.sound4012`, `OAI.MUB6.Certificate.MixedSemantics.sound4013`, `OAI.MUB6.Certificate.MixedSemantics.sound4014`, `OAI.MUB6.Certificate.MixedSemantics.sound4023`, `OAI.MUB6.Certificate.MixedSemantics.sound4026`, `OAI.MUB6.Certificate.MixedSemantics.sound4027`, `OAI.MUB6.Certificate.MixedSemantics.sound4029`, `OAI.MUB6.Certificate.MixedSemantics.sound4031`, `OAI.MUB6.Certificate.MixedSemantics.sound4032`, `OAI.MUB6.Certificate.MixedSemantics.sound4033`, `OAI.MUB6.Certificate.MixedSemantics.sound4039`, `OAI.MUB6.Certificate.MixedSemantics.sound4050`, `OAI.MUB6.Certificate.MixedSemantics.sound4053`, `OAI.MUB6.Certificate.MixedSemantics.sound436`, `OAI.MUB6.Certificate.MixedSemantics.sound454`, `OAI.MUB6.Certificate.MixedSemantics.sound455`, `OAI.MUB6.Certificate.MixedSemantics.sound4623`, `OAI.MUB6.Certificate.MixedSemantics.sound4625`, `OAI.MUB6.Certificate.MixedSemantics.sound479`, `OAI.MUB6.Certificate.MixedSemantics.sound511`, `OAI.MUB6.Certificate.MixedSemantics.sound514`, `OAI.MUB6.Certificate.MixedSemantics.sound5176`, `OAI.MUB6.Certificate.MixedSemantics.sound5177`, `OAI.MUB6.Certificate.MixedSemantics.sound521`, `OAI.MUB6.Certificate.MixedSemantics.sound5293`, `OAI.MUB6.Certificate.MixedSemantics.sound5294`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSemantics.sound5415`, `OAI.MUB6.Certificate.MixedSemantics.sound5443`, `OAI.MUB6.Certificate.MixedSemantics.sound5452`, `OAI.MUB6.Certificate.MixedSemantics.sound5453`, `OAI.MUB6.Certificate.MixedSemantics.sound5464`, `OAI.MUB6.Certificate.MixedSemantics.sound5492`, `OAI.MUB6.Certificate.MixedSemantics.sound5498`, `OAI.MUB6.Certificate.MixedSemantics.sound644`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1098`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero733`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero863`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound11`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1472`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2190`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2194`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2221`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2222`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2280`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2320`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2343`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2351`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2360`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2389`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2403`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound488`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound522`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound794`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval106`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval109`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval116`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval120`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval124`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval130`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval133`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval134`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval145`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval146`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval149`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1553`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval159`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval167`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval173`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval182`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval203`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval207`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval214`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval218`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval225`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval231`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval243`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval245`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval249`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval255`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval257`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval258`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval263`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval270`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval273`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval278`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval292`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval323`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval331`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval334`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval344`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval348`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval353`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval368`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval370`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval371`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval377`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval380`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval389`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval391`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval394`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval401`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval403`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval41`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval414`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval444`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval475`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval477`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval52`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval54`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval6`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval77`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval91`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval99`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval113`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval119`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval208`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval222`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval271`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval359`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval360`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval362`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval384`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44`, `OAI.MUB6.Certificate.PairSemantics.boundarySound165`, `OAI.MUB6.Certificate.PairSemantics.boundarySound243`, `OAI.MUB6.Certificate.PairSemantics.boundarySound248`, `OAI.MUB6.Certificate.PairSemantics.boundarySound249`, `OAI.MUB6.Certificate.PairSemantics.boundarySound250`, `OAI.MUB6.Certificate.PairSemantics.boundarySound252`, `OAI.MUB6.Certificate.PairSemantics.boundarySound261`, `OAI.MUB6.Certificate.PairSemantics.boundarySound264`, `OAI.MUB6.Certificate.PairSemantics.boundarySound305`, `OAI.MUB6.Certificate.PairSemantics.boundarySound347`, `OAI.MUB6.Certificate.PairSemantics.boundarySound377`, `OAI.MUB6.Certificate.PairSemantics.boundarySound445`, `OAI.MUB6.Certificate.PairSemantics.boundarySound454`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49`, `OAI.MUB6.Certificate.PairSemantics.boundarySound51`, `OAI.MUB6.Certificate.PairSemantics.boundarySound56`, `OAI.MUB6.Certificate.PairSemantics.boundarySound7`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73`, `OAI.MUB6.Certificate.PairSemantics.boundarySound75`, `OAI.MUB6.Certificate.PairSemantics.boundarySound83`, `OAI.MUB6.Certificate.PairSemantics.boundarySound97`, `OAI.MUB6.Certificate.PairSemantics.sound11`, `OAI.MUB6.Certificate.PairSemantics.sound1141`, `OAI.MUB6.Certificate.PairSemantics.sound1151`, `OAI.MUB6.Certificate.PairSemantics.sound1152`, `OAI.MUB6.Certificate.PairSemantics.sound117`, `OAI.MUB6.Certificate.PairSemantics.sound1294`, `OAI.MUB6.Certificate.PairSemantics.sound1323`, `OAI.MUB6.Certificate.PairSemantics.sound1381`, `OAI.MUB6.Certificate.PairSemantics.sound1383`, `OAI.MUB6.Certificate.PairSemantics.sound1384`, `OAI.MUB6.Certificate.PairSemantics.sound1387`, `OAI.MUB6.Certificate.PairSemantics.sound1390`, `OAI.MUB6.Certificate.PairSemantics.sound1391`, `OAI.MUB6.Certificate.PairSemantics.sound1392`, `OAI.MUB6.Certificate.PairSemantics.sound1395`, `OAI.MUB6.Certificate.PairSemantics.sound1399`, `OAI.MUB6.Certificate.PairSemantics.sound1414`, `OAI.MUB6.Certificate.PairSemantics.sound1419`, `OAI.MUB6.Certificate.PairSemantics.sound1423`, `OAI.MUB6.Certificate.PairSemantics.sound1424`, `OAI.MUB6.Certificate.PairSemantics.sound1425`, `OAI.MUB6.Certificate.PairSemantics.sound1432`, `OAI.MUB6.Certificate.PairSemantics.sound1434`, `OAI.MUB6.Certificate.PairSemantics.sound1437`, `OAI.MUB6.Certificate.PairSemantics.sound1443`, `OAI.MUB6.Certificate.PairSemantics.sound1458`, `OAI.MUB6.Certificate.PairSemantics.sound1486`, `OAI.MUB6.Certificate.PairSemantics.sound1500`, `OAI.MUB6.Certificate.PairSemantics.sound1504`, `OAI.MUB6.Certificate.PairSemantics.sound1506`, `OAI.MUB6.Certificate.PairSemantics.sound1512`, `OAI.MUB6.Certificate.PairSemantics.sound1518`, `OAI.MUB6.Certificate.PairSemantics.sound1520`, `OAI.MUB6.Certificate.PairSemantics.sound1523`, `OAI.MUB6.Certificate.PairSemantics.sound1530`, `OAI.MUB6.Certificate.PairSemantics.sound1531`, `OAI.MUB6.Certificate.PairSemantics.sound1533`, `OAI.MUB6.Certificate.PairSemantics.sound1535`, `OAI.MUB6.Certificate.PairSemantics.sound1540`, `OAI.MUB6.Certificate.PairSemantics.sound1548`, `OAI.MUB6.Certificate.PairSemantics.sound1552`, `OAI.MUB6.Certificate.PairSemantics.sound1563`, `OAI.MUB6.Certificate.PairSemantics.sound1585`, `OAI.MUB6.Certificate.PairSemantics.sound1605`, `OAI.MUB6.Certificate.PairSemantics.sound1614`, `OAI.MUB6.Certificate.PairSemantics.sound1617`, `OAI.MUB6.Certificate.PairSemantics.sound1624`, `OAI.MUB6.Certificate.PairSemantics.sound1625`, `OAI.MUB6.Certificate.PairSemantics.sound1627`, `OAI.MUB6.Certificate.PairSemantics.sound1628`, `OAI.MUB6.Certificate.PairSemantics.sound1631`, `OAI.MUB6.Certificate.PairSemantics.sound1634`, `OAI.MUB6.Certificate.PairSemantics.sound1635`, `OAI.MUB6.Certificate.PairSemantics.sound1637`, `OAI.MUB6.Certificate.PairSemantics.sound1638`, `OAI.MUB6.Certificate.PairSemantics.sound1643`, `OAI.MUB6.Certificate.PairSemantics.sound1646`, `OAI.MUB6.Certificate.PairSemantics.sound1648`, `OAI.MUB6.Certificate.PairSemantics.sound1652`, `OAI.MUB6.Certificate.PairSemantics.sound1668`, `OAI.MUB6.Certificate.PairSemantics.sound1669`, `OAI.MUB6.Certificate.PairSemantics.sound1682`, `OAI.MUB6.Certificate.PairSemantics.sound1685`, `OAI.MUB6.Certificate.PairSemantics.sound1686`, `OAI.MUB6.Certificate.PairSemantics.sound1707`, `OAI.MUB6.Certificate.PairSemantics.sound1716`, `OAI.MUB6.Certificate.PairSemantics.sound1718`, `OAI.MUB6.Certificate.PairSemantics.sound1736`, `OAI.MUB6.Certificate.PairSemantics.sound1739`, `OAI.MUB6.Certificate.PairSemantics.sound1768`, `OAI.MUB6.Certificate.PairSemantics.sound1769`, `OAI.MUB6.Certificate.PairSemantics.sound1770`, `OAI.MUB6.Certificate.PairSemantics.sound1774`, `OAI.MUB6.Certificate.PairSemantics.sound1784`, `OAI.MUB6.Certificate.PairSemantics.sound1793`, `OAI.MUB6.Certificate.PairSemantics.sound1800`, `OAI.MUB6.Certificate.PairSemantics.sound1803`, `OAI.MUB6.Certificate.PairSemantics.sound1826`, `OAI.MUB6.Certificate.PairSemantics.sound1828`, `OAI.MUB6.Certificate.PairSemantics.sound1830`, `OAI.MUB6.Certificate.PairSemantics.sound1849`, `OAI.MUB6.Certificate.PairSemantics.sound1858`, `OAI.MUB6.Certificate.PairSemantics.sound1860`, `OAI.MUB6.Certificate.PairSemantics.sound1865`, `OAI.MUB6.Certificate.PairSemantics.sound1866`, `OAI.MUB6.Certificate.PairSemantics.sound1867`, `OAI.MUB6.Certificate.PairSemantics.sound1869`, `OAI.MUB6.Certificate.PairSemantics.sound1870`, `OAI.MUB6.Certificate.PairSemantics.sound1872`, `OAI.MUB6.Certificate.PairSemantics.sound1873`, `OAI.MUB6.Certificate.PairSemantics.sound1879`, `OAI.MUB6.Certificate.PairSemantics.sound1885`, `OAI.MUB6.Certificate.PairSemantics.sound1890`, `OAI.MUB6.Certificate.PairSemantics.sound1938`, `OAI.MUB6.Certificate.PairSemantics.sound1968`, `OAI.MUB6.Certificate.PairSemantics.sound1977`, `OAI.MUB6.Certificate.PairSemantics.sound1978`, `OAI.MUB6.Certificate.PairSemantics.sound1980`, `OAI.MUB6.Certificate.PairSemantics.sound1986`, `OAI.MUB6.Certificate.PairSemantics.sound1987`, `OAI.MUB6.Certificate.PairSemantics.sound2041`, `OAI.MUB6.Certificate.PairSemantics.sound2058`, `OAI.MUB6.Certificate.PairSemantics.sound2106`, `OAI.MUB6.Certificate.PairSemantics.sound2108`, `OAI.MUB6.Certificate.PairSemantics.sound2113`, `OAI.MUB6.Certificate.PairSemantics.sound2117`, `OAI.MUB6.Certificate.PairSemantics.sound2122`, `OAI.MUB6.Certificate.PairSemantics.sound2123`, `OAI.MUB6.Certificate.PairSemantics.sound2128`, `OAI.MUB6.Certificate.PairSemantics.sound2132`, `OAI.MUB6.Certificate.PairSemantics.sound2152`, `OAI.MUB6.Certificate.PairSemantics.sound2168`, `OAI.MUB6.Certificate.PairSemantics.sound2175`, `OAI.MUB6.Certificate.PairSemantics.sound2177`, `OAI.MUB6.Certificate.PairSemantics.sound2183`, `OAI.MUB6.Certificate.PairSemantics.sound2190`, `OAI.MUB6.Certificate.PairSemantics.sound2192`, `OAI.MUB6.Certificate.PairSemantics.sound2197`, `OAI.MUB6.Certificate.PairSemantics.sound2201`, `OAI.MUB6.Certificate.PairSemantics.sound2202`, `OAI.MUB6.Certificate.PairSemantics.sound2204`, `OAI.MUB6.Certificate.PairSemantics.sound2213`, `OAI.MUB6.Certificate.PairSemantics.sound2216`, `OAI.MUB6.Certificate.PairSemantics.sound2228`, `OAI.MUB6.Certificate.PairSemantics.sound2243`, `OAI.MUB6.Certificate.PairSemantics.sound2244`, `OAI.MUB6.Certificate.PairSemantics.sound2262`, `OAI.MUB6.Certificate.PairSemantics.sound2284`, `OAI.MUB6.Certificate.PairSemantics.sound2285`, `OAI.MUB6.Certificate.PairSemantics.sound2286`, `OAI.MUB6.Certificate.PairSemantics.sound2293`, `OAI.MUB6.Certificate.PairSemantics.sound2294`, `OAI.MUB6.Certificate.PairSemantics.sound2295`, `OAI.MUB6.Certificate.PairSemantics.sound2296`, `OAI.MUB6.Certificate.PairSemantics.sound2298`, `OAI.MUB6.Certificate.PairSemantics.sound2304`, `OAI.MUB6.Certificate.PairSemantics.sound2307`, `OAI.MUB6.Certificate.PairSemantics.sound2312`, `OAI.MUB6.Certificate.PairSemantics.sound2315`, `OAI.MUB6.Certificate.PairSemantics.sound232`, `OAI.MUB6.Certificate.PairSemantics.sound2324`, `OAI.MUB6.Certificate.PairSemantics.sound2325`, `OAI.MUB6.Certificate.PairSemantics.sound2327`, `OAI.MUB6.Certificate.PairSemantics.sound2338`, `OAI.MUB6.Certificate.PairSemantics.sound2349`, `OAI.MUB6.Certificate.PairSemantics.sound2357`, `OAI.MUB6.Certificate.PairSemantics.sound2375`, `OAI.MUB6.Certificate.PairSemantics.sound2382`, `OAI.MUB6.Certificate.PairSemantics.sound2389`, `OAI.MUB6.Certificate.PairSemantics.sound2390`, `OAI.MUB6.Certificate.PairSemantics.sound2391`, `OAI.MUB6.Certificate.PairSemantics.sound2399`, `OAI.MUB6.Certificate.PairSemantics.sound2400`, `OAI.MUB6.Certificate.PairSemantics.sound2403`, `OAI.MUB6.Certificate.PairSemantics.sound2411`, `OAI.MUB6.Certificate.PairSemantics.sound2413`, `OAI.MUB6.Certificate.PairSemantics.sound2414`, `OAI.MUB6.Certificate.PairSemantics.sound2415`, `OAI.MUB6.Certificate.PairSemantics.sound2416`, `OAI.MUB6.Certificate.PairSemantics.sound2417`, `OAI.MUB6.Certificate.PairSemantics.sound2420`, `OAI.MUB6.Certificate.PairSemantics.sound2428`, `OAI.MUB6.Certificate.PairSemantics.sound2433`, `OAI.MUB6.Certificate.PairSemantics.sound2434`, `OAI.MUB6.Certificate.PairSemantics.sound2435`, `OAI.MUB6.Certificate.PairSemantics.sound2436`, `OAI.MUB6.Certificate.PairSemantics.sound2440`, `OAI.MUB6.Certificate.PairSemantics.sound2441`, `OAI.MUB6.Certificate.PairSemantics.sound2442`, `OAI.MUB6.Certificate.PairSemantics.sound2443`, `OAI.MUB6.Certificate.PairSemantics.sound2444`, `OAI.MUB6.Certificate.PairSemantics.sound2445`, `OAI.MUB6.Certificate.PairSemantics.sound2455`, `OAI.MUB6.Certificate.PairSemantics.sound2456`, `OAI.MUB6.Certificate.PairSemantics.sound2457`, `OAI.MUB6.Certificate.PairSemantics.sound2462`, `OAI.MUB6.Certificate.PairSemantics.sound2463`, `OAI.MUB6.Certificate.PairSemantics.sound2464`, `OAI.MUB6.Certificate.PairSemantics.sound2465`, `OAI.MUB6.Certificate.PairSemantics.sound2466`, `OAI.MUB6.Certificate.PairSemantics.sound2470`, `OAI.MUB6.Certificate.PairSemantics.sound2472`, `OAI.MUB6.Certificate.PairSemantics.sound2473`, `OAI.MUB6.Certificate.PairSemantics.sound2477`, `OAI.MUB6.Certificate.PairSemantics.sound2479`, `OAI.MUB6.Certificate.PairSemantics.sound2486`, `OAI.MUB6.Certificate.PairSemantics.sound2489`, `OAI.MUB6.Certificate.PairSemantics.sound2490`, `OAI.MUB6.Certificate.PairSemantics.sound2491`, `OAI.MUB6.Certificate.PairSemantics.sound2492`, `OAI.MUB6.Certificate.PairSemantics.sound2507`, `OAI.MUB6.Certificate.PairSemantics.sound2520`, `OAI.MUB6.Certificate.PairSemantics.sound2521`, `OAI.MUB6.Certificate.PairSemantics.sound2524`, `OAI.MUB6.Certificate.PairSemantics.sound2525`, `OAI.MUB6.Certificate.PairSemantics.sound2533`, `OAI.MUB6.Certificate.PairSemantics.sound2540`, `OAI.MUB6.Certificate.PairSemantics.sound2546`, `OAI.MUB6.Certificate.PairSemantics.sound2547`, `OAI.MUB6.Certificate.PairSemantics.sound2548`, `OAI.MUB6.Certificate.PairSemantics.sound2557`, `OAI.MUB6.Certificate.PairSemantics.sound2558`, `OAI.MUB6.Certificate.PairSemantics.sound2559`, `OAI.MUB6.Certificate.PairSemantics.sound2564`, `OAI.MUB6.Certificate.PairSemantics.sound2565`, `OAI.MUB6.Certificate.PairSemantics.sound2566`, `OAI.MUB6.Certificate.PairSemantics.sound2573`, `OAI.MUB6.Certificate.PairSemantics.sound2578`, `OAI.MUB6.Certificate.PairSemantics.sound2579`, `OAI.MUB6.Certificate.PairSemantics.sound2580`, `OAI.MUB6.Certificate.PairSemantics.sound2602`, `OAI.MUB6.Certificate.PairSemantics.sound2604`, `OAI.MUB6.Certificate.PairSemantics.sound2606`, `OAI.MUB6.Certificate.PairSemantics.sound2619`, `OAI.MUB6.Certificate.PairSemantics.sound2626`, `OAI.MUB6.Certificate.PairSemantics.sound2627`, `OAI.MUB6.Certificate.PairSemantics.sound2641`, `OAI.MUB6.Certificate.PairSemantics.sound2657`, `OAI.MUB6.Certificate.PairSemantics.sound2658`, `OAI.MUB6.Certificate.PairSemantics.sound2661`, `OAI.MUB6.Certificate.PairSemantics.sound2666`, `OAI.MUB6.Certificate.PairSemantics.sound2670`, `OAI.MUB6.Certificate.PairSemantics.sound2671`, `OAI.MUB6.Certificate.PairSemantics.sound2674`, `OAI.MUB6.Certificate.PairSemantics.sound2683`, `OAI.MUB6.Certificate.PairSemantics.sound2686`, `OAI.MUB6.Certificate.PairSemantics.sound2690`, `OAI.MUB6.Certificate.PairSemantics.sound2693`, `OAI.MUB6.Certificate.PairSemantics.sound2709`, `OAI.MUB6.Certificate.PairSemantics.sound2710`, `OAI.MUB6.Certificate.PairSemantics.sound2711`, `OAI.MUB6.Certificate.PairSemantics.sound2714`, `OAI.MUB6.Certificate.PairSemantics.sound2717`, `OAI.MUB6.Certificate.PairSemantics.sound2723`, `OAI.MUB6.Certificate.PairSemantics.sound2732`, `OAI.MUB6.Certificate.PairSemantics.sound2733`, `OAI.MUB6.Certificate.PairSemantics.sound2754`, `OAI.MUB6.Certificate.PairSemantics.sound2757`, `OAI.MUB6.Certificate.PairSemantics.sound2765`, `OAI.MUB6.Certificate.PairSemantics.sound2788`, `OAI.MUB6.Certificate.PairSemantics.sound2790`, `OAI.MUB6.Certificate.PairSemantics.sound2793`, `OAI.MUB6.Certificate.PairSemantics.sound2827`, `OAI.MUB6.Certificate.PairSemantics.sound2829`, `OAI.MUB6.Certificate.PairSemantics.sound2836`, `OAI.MUB6.Certificate.PairSemantics.sound2839`, `OAI.MUB6.Certificate.PairSemantics.sound284`, `OAI.MUB6.Certificate.PairSemantics.sound2845`, `OAI.MUB6.Certificate.PairSemantics.sound2850`, `OAI.MUB6.Certificate.PairSemantics.sound2852`, `OAI.MUB6.Certificate.PairSemantics.sound2854`, `OAI.MUB6.Certificate.PairSemantics.sound2855`, `OAI.MUB6.Certificate.PairSemantics.sound2863`, `OAI.MUB6.Certificate.PairSemantics.sound2864`, `OAI.MUB6.Certificate.PairSemantics.sound2865`, `OAI.MUB6.Certificate.PairSemantics.sound2866`, `OAI.MUB6.Certificate.PairSemantics.sound2867`, `OAI.MUB6.Certificate.PairSemantics.sound2868`, `OAI.MUB6.Certificate.PairSemantics.sound2872`, `OAI.MUB6.Certificate.PairSemantics.sound2873`, `OAI.MUB6.Certificate.PairSemantics.sound2874`, `OAI.MUB6.Certificate.PairSemantics.sound2875`, `OAI.MUB6.Certificate.PairSemantics.sound2878`, `OAI.MUB6.Certificate.PairSemantics.sound2879`, `OAI.MUB6.Certificate.PairSemantics.sound2880`, `OAI.MUB6.Certificate.PairSemantics.sound2881`, `OAI.MUB6.Certificate.PairSemantics.sound2882`, `OAI.MUB6.Certificate.PairSemantics.sound2883`, `OAI.MUB6.Certificate.PairSemantics.sound2884`, `OAI.MUB6.Certificate.PairSemantics.sound2886`, `OAI.MUB6.Certificate.PairSemantics.sound2887`, `OAI.MUB6.Certificate.PairSemantics.sound2888`, `OAI.MUB6.Certificate.PairSemantics.sound2889`, `OAI.MUB6.Certificate.PairSemantics.sound2890`, `OAI.MUB6.Certificate.PairSemantics.sound2891`, `OAI.MUB6.Certificate.PairSemantics.sound2892`, `OAI.MUB6.Certificate.PairSemantics.sound2894`, `OAI.MUB6.Certificate.PairSemantics.sound2895`, `OAI.MUB6.Certificate.PairSemantics.sound2896`, `OAI.MUB6.Certificate.PairSemantics.sound2897`, `OAI.MUB6.Certificate.PairSemantics.sound2898`, `OAI.MUB6.Certificate.PairSemantics.sound2899`, `OAI.MUB6.Certificate.PairSemantics.sound2900`, `OAI.MUB6.Certificate.PairSemantics.sound2901`, `OAI.MUB6.Certificate.PairSemantics.sound2902`, `OAI.MUB6.Certificate.PairSemantics.sound2903`, `OAI.MUB6.Certificate.PairSemantics.sound2906`, `OAI.MUB6.Certificate.PairSemantics.sound2909`, `OAI.MUB6.Certificate.PairSemantics.sound2910`, `OAI.MUB6.Certificate.PairSemantics.sound2912`, `OAI.MUB6.Certificate.PairSemantics.sound2913`, `OAI.MUB6.Certificate.PairSemantics.sound2914`, `OAI.MUB6.Certificate.PairSemantics.sound2915`, `OAI.MUB6.Certificate.PairSemantics.sound2916`, `OAI.MUB6.Certificate.PairSemantics.sound2917`, `OAI.MUB6.Certificate.PairSemantics.sound2918`, `OAI.MUB6.Certificate.PairSemantics.sound2919`, `OAI.MUB6.Certificate.PairSemantics.sound2920`, `OAI.MUB6.Certificate.PairSemantics.sound2922`, `OAI.MUB6.Certificate.PairSemantics.sound2924`, `OAI.MUB6.Certificate.PairSemantics.sound2927`, `OAI.MUB6.Certificate.PairSemantics.sound2928`, `OAI.MUB6.Certificate.PairSemantics.sound2929`, `OAI.MUB6.Certificate.PairSemantics.sound2930`, `OAI.MUB6.Certificate.PairSemantics.sound2931`, `OAI.MUB6.Certificate.PairSemantics.sound2933`, `OAI.MUB6.Certificate.PairSemantics.sound2934`, `OAI.MUB6.Certificate.PairSemantics.sound2935`, `OAI.MUB6.Certificate.PairSemantics.sound2936`, `OAI.MUB6.Certificate.PairSemantics.sound2939`, `OAI.MUB6.Certificate.PairSemantics.sound2940`, `OAI.MUB6.Certificate.PairSemantics.sound2941`, `OAI.MUB6.Certificate.PairSemantics.sound2943`, `OAI.MUB6.Certificate.PairSemantics.sound2944`, `OAI.MUB6.Certificate.PairSemantics.sound2947`, `OAI.MUB6.Certificate.PairSemantics.sound2948`, `OAI.MUB6.Certificate.PairSemantics.sound2949`, `OAI.MUB6.Certificate.PairSemantics.sound2950`, `OAI.MUB6.Certificate.PairSemantics.sound2952`, `OAI.MUB6.Certificate.PairSemantics.sound2953`, `OAI.MUB6.Certificate.PairSemantics.sound2954`, `OAI.MUB6.Certificate.PairSemantics.sound2955`, `OAI.MUB6.Certificate.PairSemantics.sound2956`, `OAI.MUB6.Certificate.PairSemantics.sound2957`, `OAI.MUB6.Certificate.PairSemantics.sound2958`, `OAI.MUB6.Certificate.PairSemantics.sound2959`, `OAI.MUB6.Certificate.PairSemantics.sound2960`, `OAI.MUB6.Certificate.PairSemantics.sound2962`, `OAI.MUB6.Certificate.PairSemantics.sound2964`, `OAI.MUB6.Certificate.PairSemantics.sound2965`, `OAI.MUB6.Certificate.PairSemantics.sound2966`, `OAI.MUB6.Certificate.PairSemantics.sound2967`, `OAI.MUB6.Certificate.PairSemantics.sound2968`, `OAI.MUB6.Certificate.PairSemantics.sound2969`, `OAI.MUB6.Certificate.PairSemantics.sound2970`, `OAI.MUB6.Certificate.PairSemantics.sound2972`, `OAI.MUB6.Certificate.PairSemantics.sound2973`, `OAI.MUB6.Certificate.PairSemantics.sound2974`, `OAI.MUB6.Certificate.PairSemantics.sound2975`, `OAI.MUB6.Certificate.PairSemantics.sound2976`, `OAI.MUB6.Certificate.PairSemantics.sound2977`, `OAI.MUB6.Certificate.PairSemantics.sound2979`, `OAI.MUB6.Certificate.PairSemantics.sound2980`, `OAI.MUB6.Certificate.PairSemantics.sound2982`, `OAI.MUB6.Certificate.PairSemantics.sound2985`, `OAI.MUB6.Certificate.PairSemantics.sound2986`, `OAI.MUB6.Certificate.PairSemantics.sound2987`, `OAI.MUB6.Certificate.PairSemantics.sound2988`, `OAI.MUB6.Certificate.PairSemantics.sound2989`, `OAI.MUB6.Certificate.PairSemantics.sound2990`, `OAI.MUB6.Certificate.PairSemantics.sound2991`, `OAI.MUB6.Certificate.PairSemantics.sound2993`, `OAI.MUB6.Certificate.PairSemantics.sound2994`, `OAI.MUB6.Certificate.PairSemantics.sound2996`, `OAI.MUB6.Certificate.PairSemantics.sound2997`, `OAI.MUB6.Certificate.PairSemantics.sound2998`, `OAI.MUB6.Certificate.PairSemantics.sound2999`, `OAI.MUB6.Certificate.PairSemantics.sound3000`, `OAI.MUB6.Certificate.PairSemantics.sound3001`, `OAI.MUB6.Certificate.PairSemantics.sound3002`, `OAI.MUB6.Certificate.PairSemantics.sound3004`, `OAI.MUB6.Certificate.PairSemantics.sound3006`, `OAI.MUB6.Certificate.PairSemantics.sound3009`, `OAI.MUB6.Certificate.PairSemantics.sound3010`, `OAI.MUB6.Certificate.PairSemantics.sound3011`, `OAI.MUB6.Certificate.PairSemantics.sound3012`, `OAI.MUB6.Certificate.PairSemantics.sound3013`, `OAI.MUB6.Certificate.PairSemantics.sound3014`, `OAI.MUB6.Certificate.PairSemantics.sound3015`, `OAI.MUB6.Certificate.PairSemantics.sound3016`, `OAI.MUB6.Certificate.PairSemantics.sound3017`, `OAI.MUB6.Certificate.PairSemantics.sound3018`, `OAI.MUB6.Certificate.PairSemantics.sound3019`, `OAI.MUB6.Certificate.PairSemantics.sound3020`, `OAI.MUB6.Certificate.PairSemantics.sound3021`, `OAI.MUB6.Certificate.PairSemantics.sound3022`, `OAI.MUB6.Certificate.PairSemantics.sound3023`, `OAI.MUB6.Certificate.PairSemantics.sound3024`, `OAI.MUB6.Certificate.PairSemantics.sound3025`, `OAI.MUB6.Certificate.PairSemantics.sound3026`, `OAI.MUB6.Certificate.PairSemantics.sound3027`, `OAI.MUB6.Certificate.PairSemantics.sound3028`, `OAI.MUB6.Certificate.PairSemantics.sound3029`, `OAI.MUB6.Certificate.PairSemantics.sound3030`, `OAI.MUB6.Certificate.PairSemantics.sound3031`, `OAI.MUB6.Certificate.PairSemantics.sound3032`, `OAI.MUB6.Certificate.PairSemantics.sound3033`, `OAI.MUB6.Certificate.PairSemantics.sound3034`, `OAI.MUB6.Certificate.PairSemantics.sound3035`, `OAI.MUB6.Certificate.PairSemantics.sound3036`, `OAI.MUB6.Certificate.PairSemantics.sound3038`, `OAI.MUB6.Certificate.PairSemantics.sound3039`, `OAI.MUB6.Certificate.PairSemantics.sound3040`, `OAI.MUB6.Certificate.PairSemantics.sound3041`, `OAI.MUB6.Certificate.PairSemantics.sound3042`, `OAI.MUB6.Certificate.PairSemantics.sound3043`, `OAI.MUB6.Certificate.PairSemantics.sound3044`, `OAI.MUB6.Certificate.PairSemantics.sound3045`, `OAI.MUB6.Certificate.PairSemantics.sound3047`, `OAI.MUB6.Certificate.PairSemantics.sound3048`, `OAI.MUB6.Certificate.PairSemantics.sound3049`, `OAI.MUB6.Certificate.PairSemantics.sound3050`, `OAI.MUB6.Certificate.PairSemantics.sound3051`, `OAI.MUB6.Certificate.PairSemantics.sound3053`, `OAI.MUB6.Certificate.PairSemantics.sound3054`, `OAI.MUB6.Certificate.PairSemantics.sound3056`, `OAI.MUB6.Certificate.PairSemantics.sound3058`, `OAI.MUB6.Certificate.PairSemantics.sound3059`, `OAI.MUB6.Certificate.PairSemantics.sound3060`, `OAI.MUB6.Certificate.PairSemantics.sound3061`, `OAI.MUB6.Certificate.PairSemantics.sound3062`, `OAI.MUB6.Certificate.PairSemantics.sound3063`, `OAI.MUB6.Certificate.PairSemantics.sound3065`, `OAI.MUB6.Certificate.PairSemantics.sound3066`, `OAI.MUB6.Certificate.PairSemantics.sound3067`, `OAI.MUB6.Certificate.PairSemantics.sound3068`, `OAI.MUB6.Certificate.PairSemantics.sound3069`, `OAI.MUB6.Certificate.PairSemantics.sound3071`, `OAI.MUB6.Certificate.PairSemantics.sound3072`, `OAI.MUB6.Certificate.PairSemantics.sound3073`, `OAI.MUB6.Certificate.PairSemantics.sound3074`, `OAI.MUB6.Certificate.PairSemantics.sound3075`, `OAI.MUB6.Certificate.PairSemantics.sound3076`, `OAI.MUB6.Certificate.PairSemantics.sound3077`, `OAI.MUB6.Certificate.PairSemantics.sound3078`, `OAI.MUB6.Certificate.PairSemantics.sound3079`, `OAI.MUB6.Certificate.PairSemantics.sound3080`, `OAI.MUB6.Certificate.PairSemantics.sound3081`, `OAI.MUB6.Certificate.PairSemantics.sound3082`, `OAI.MUB6.Certificate.PairSemantics.sound3083`, `OAI.MUB6.Certificate.PairSemantics.sound3084`, `OAI.MUB6.Certificate.PairSemantics.sound3085`, `OAI.MUB6.Certificate.PairSemantics.sound3086`, `OAI.MUB6.Certificate.PairSemantics.sound3090`, `OAI.MUB6.Certificate.PairSemantics.sound3091`, `OAI.MUB6.Certificate.PairSemantics.sound3092`, `OAI.MUB6.Certificate.PairSemantics.sound3093`, `OAI.MUB6.Certificate.PairSemantics.sound3094`, `OAI.MUB6.Certificate.PairSemantics.sound3095`, `OAI.MUB6.Certificate.PairSemantics.sound3096`, `OAI.MUB6.Certificate.PairSemantics.sound3097`, `OAI.MUB6.Certificate.PairSemantics.sound3098`, `OAI.MUB6.Certificate.PairSemantics.sound3099`, `OAI.MUB6.Certificate.PairSemantics.sound3100`, `OAI.MUB6.Certificate.PairSemantics.sound3101`, `OAI.MUB6.Certificate.PairSemantics.sound3102`, `OAI.MUB6.Certificate.PairSemantics.sound3105`, `OAI.MUB6.Certificate.PairSemantics.sound3106`, `OAI.MUB6.Certificate.PairSemantics.sound3107`, `OAI.MUB6.Certificate.PairSemantics.sound3108`, `OAI.MUB6.Certificate.PairSemantics.sound3109`, `OAI.MUB6.Certificate.PairSemantics.sound3110`, `OAI.MUB6.Certificate.PairSemantics.sound3111`, `OAI.MUB6.Certificate.PairSemantics.sound3112`, `OAI.MUB6.Certificate.PairSemantics.sound3113`, `OAI.MUB6.Certificate.PairSemantics.sound3114`, `OAI.MUB6.Certificate.PairSemantics.sound3115`, `OAI.MUB6.Certificate.PairSemantics.sound3116`, `OAI.MUB6.Certificate.PairSemantics.sound3118`, `OAI.MUB6.Certificate.PairSemantics.sound3119`, `OAI.MUB6.Certificate.PairSemantics.sound3120`, `OAI.MUB6.Certificate.PairSemantics.sound3121`, `OAI.MUB6.Certificate.PairSemantics.sound3122`, `OAI.MUB6.Certificate.PairSemantics.sound3123`, `OAI.MUB6.Certificate.PairSemantics.sound3124`, `OAI.MUB6.Certificate.PairSemantics.sound3125`, `OAI.MUB6.Certificate.PairSemantics.sound3128`, `OAI.MUB6.Certificate.PairSemantics.sound3129`, `OAI.MUB6.Certificate.PairSemantics.sound3130`, `OAI.MUB6.Certificate.PairSemantics.sound3131`, `OAI.MUB6.Certificate.PairSemantics.sound3133`, `OAI.MUB6.Certificate.PairSemantics.sound3135`, `OAI.MUB6.Certificate.PairSemantics.sound3136`, `OAI.MUB6.Certificate.PairSemantics.sound3138`, `OAI.MUB6.Certificate.PairSemantics.sound3139`, `OAI.MUB6.Certificate.PairSemantics.sound3140`, `OAI.MUB6.Certificate.PairSemantics.sound3141`, `OAI.MUB6.Certificate.PairSemantics.sound3142`, `OAI.MUB6.Certificate.PairSemantics.sound3144`, `OAI.MUB6.Certificate.PairSemantics.sound3145`, `OAI.MUB6.Certificate.PairSemantics.sound3146`, `OAI.MUB6.Certificate.PairSemantics.sound3150`, `OAI.MUB6.Certificate.PairSemantics.sound3151`, `OAI.MUB6.Certificate.PairSemantics.sound3152`, `OAI.MUB6.Certificate.PairSemantics.sound3153`, `OAI.MUB6.Certificate.PairSemantics.sound3155`, `OAI.MUB6.Certificate.PairSemantics.sound3158`, `OAI.MUB6.Certificate.PairSemantics.sound3159`, `OAI.MUB6.Certificate.PairSemantics.sound3160`, `OAI.MUB6.Certificate.PairSemantics.sound3161`, `OAI.MUB6.Certificate.PairSemantics.sound3162`, `OAI.MUB6.Certificate.PairSemantics.sound3163`, `OAI.MUB6.Certificate.PairSemantics.sound3164`, `OAI.MUB6.Certificate.PairSemantics.sound3166`, `OAI.MUB6.Certificate.PairSemantics.sound3167`, `OAI.MUB6.Certificate.PairSemantics.sound3168`, `OAI.MUB6.Certificate.PairSemantics.sound3169`, `OAI.MUB6.Certificate.PairSemantics.sound3170`, `OAI.MUB6.Certificate.PairSemantics.sound3171`, `OAI.MUB6.Certificate.PairSemantics.sound3172`, `OAI.MUB6.Certificate.PairSemantics.sound3173`, `OAI.MUB6.Certificate.PairSemantics.sound3174`, `OAI.MUB6.Certificate.PairSemantics.sound3176`, `OAI.MUB6.Certificate.PairSemantics.sound3178`, `OAI.MUB6.Certificate.PairSemantics.sound3179`, `OAI.MUB6.Certificate.PairSemantics.sound3180`, `OAI.MUB6.Certificate.PairSemantics.sound3181`, `OAI.MUB6.Certificate.PairSemantics.sound3183`, `OAI.MUB6.Certificate.PairSemantics.sound3184`, `OAI.MUB6.Certificate.PairSemantics.sound3185`, `OAI.MUB6.Certificate.PairSemantics.sound3186`, `OAI.MUB6.Certificate.PairSemantics.sound3187`, `OAI.MUB6.Certificate.PairSemantics.sound3188`, `OAI.MUB6.Certificate.PairSemantics.sound3189`, `OAI.MUB6.Certificate.PairSemantics.sound3191`, `OAI.MUB6.Certificate.PairSemantics.sound3192`, `OAI.MUB6.Certificate.PairSemantics.sound3193`, `OAI.MUB6.Certificate.PairSemantics.sound3194`, `OAI.MUB6.Certificate.PairSemantics.sound3195`, `OAI.MUB6.Certificate.PairSemantics.sound3196`, `OAI.MUB6.Certificate.PairSemantics.sound3197`, `OAI.MUB6.Certificate.PairSemantics.sound3198`, `OAI.MUB6.Certificate.PairSemantics.sound3199`, `OAI.MUB6.Certificate.PairSemantics.sound3200`, `OAI.MUB6.Certificate.PairSemantics.sound3201`, `OAI.MUB6.Certificate.PairSemantics.sound3202`, `OAI.MUB6.Certificate.PairSemantics.sound3203`, `OAI.MUB6.Certificate.PairSemantics.sound3204`, `OAI.MUB6.Certificate.PairSemantics.sound3205`, `OAI.MUB6.Certificate.PairSemantics.sound3206`, `OAI.MUB6.Certificate.PairSemantics.sound3208`, `OAI.MUB6.Certificate.PairSemantics.sound3211`, `OAI.MUB6.Certificate.PairSemantics.sound3212`, `OAI.MUB6.Certificate.PairSemantics.sound3213`, `OAI.MUB6.Certificate.PairSemantics.sound3214`, `OAI.MUB6.Certificate.PairSemantics.sound3215`, `OAI.MUB6.Certificate.PairSemantics.sound3216`, `OAI.MUB6.Certificate.PairSemantics.sound3217`, `OAI.MUB6.Certificate.PairSemantics.sound3218`, `OAI.MUB6.Certificate.PairSemantics.sound3219`, `OAI.MUB6.Certificate.PairSemantics.sound3221`, `OAI.MUB6.Certificate.PairSemantics.sound3222`, `OAI.MUB6.Certificate.PairSemantics.sound3223`, `OAI.MUB6.Certificate.PairSemantics.sound3224`, `OAI.MUB6.Certificate.PairSemantics.sound3226`, `OAI.MUB6.Certificate.PairSemantics.sound3227`, `OAI.MUB6.Certificate.PairSemantics.sound3228`, `OAI.MUB6.Certificate.PairSemantics.sound3230`, `OAI.MUB6.Certificate.PairSemantics.sound3231`, `OAI.MUB6.Certificate.PairSemantics.sound3233`, `OAI.MUB6.Certificate.PairSemantics.sound3234`, `OAI.MUB6.Certificate.PairSemantics.sound3235`, `OAI.MUB6.Certificate.PairSemantics.sound3237`, `OAI.MUB6.Certificate.PairSemantics.sound3238`, `OAI.MUB6.Certificate.PairSemantics.sound3239`, `OAI.MUB6.Certificate.PairSemantics.sound3240`, `OAI.MUB6.Certificate.PairSemantics.sound3241`, `OAI.MUB6.Certificate.PairSemantics.sound3242`, `OAI.MUB6.Certificate.PairSemantics.sound3243`, `OAI.MUB6.Certificate.PairSemantics.sound3244`, `OAI.MUB6.Certificate.PairSemantics.sound3246`, `OAI.MUB6.Certificate.PairSemantics.sound3247`, `OAI.MUB6.Certificate.PairSemantics.sound3248`, `OAI.MUB6.Certificate.PairSemantics.sound3249`, `OAI.MUB6.Certificate.PairSemantics.sound3250`, `OAI.MUB6.Certificate.PairSemantics.sound3251`, `OAI.MUB6.Certificate.PairSemantics.sound3253`, `OAI.MUB6.Certificate.PairSemantics.sound3254`, `OAI.MUB6.Certificate.PairSemantics.sound3255`, `OAI.MUB6.Certificate.PairSemantics.sound3256`, `OAI.MUB6.Certificate.PairSemantics.sound3258`, `OAI.MUB6.Certificate.PairSemantics.sound3259`, `OAI.MUB6.Certificate.PairSemantics.sound3261`, `OAI.MUB6.Certificate.PairSemantics.sound3262`, `OAI.MUB6.Certificate.PairSemantics.sound3263`, `OAI.MUB6.Certificate.PairSemantics.sound3266`, `OAI.MUB6.Certificate.PairSemantics.sound3267`, `OAI.MUB6.Certificate.PairSemantics.sound3268`, `OAI.MUB6.Certificate.PairSemantics.sound3269`, `OAI.MUB6.Certificate.PairSemantics.sound3270`, `OAI.MUB6.Certificate.PairSemantics.sound3271`, `OAI.MUB6.Certificate.PairSemantics.sound3273`, `OAI.MUB6.Certificate.PairSemantics.sound3275`, `OAI.MUB6.Certificate.PairSemantics.sound3276`, `OAI.MUB6.Certificate.PairSemantics.sound3277`, `OAI.MUB6.Certificate.PairSemantics.sound3279`, `OAI.MUB6.Certificate.PairSemantics.sound3280`, `OAI.MUB6.Certificate.PairSemantics.sound3281`, `OAI.MUB6.Certificate.PairSemantics.sound3282`, `OAI.MUB6.Certificate.PairSemantics.sound3283`, `OAI.MUB6.Certificate.PairSemantics.sound3284`, `OAI.MUB6.Certificate.PairSemantics.sound3288`, `OAI.MUB6.Certificate.PairSemantics.sound3289`, `OAI.MUB6.Certificate.PairSemantics.sound3290`, `OAI.MUB6.Certificate.PairSemantics.sound3291`, `OAI.MUB6.Certificate.PairSemantics.sound3292`, `OAI.MUB6.Certificate.PairSemantics.sound3293`, `OAI.MUB6.Certificate.PairSemantics.sound3294`, `OAI.MUB6.Certificate.PairSemantics.sound3295`, `OAI.MUB6.Certificate.PairSemantics.sound3296`, `OAI.MUB6.Certificate.PairSemantics.sound3297`, `OAI.MUB6.Certificate.PairSemantics.sound3298`, `OAI.MUB6.Certificate.PairSemantics.sound3299`, `OAI.MUB6.Certificate.PairSemantics.sound3300`, `OAI.MUB6.Certificate.PairSemantics.sound3301`, `OAI.MUB6.Certificate.PairSemantics.sound3302`, `OAI.MUB6.Certificate.PairSemantics.sound3303`, `OAI.MUB6.Certificate.PairSemantics.sound3304`, `OAI.MUB6.Certificate.PairSemantics.sound3305`, `OAI.MUB6.Certificate.PairSemantics.sound3307`, `OAI.MUB6.Certificate.PairSemantics.sound3308`, `OAI.MUB6.Certificate.PairSemantics.sound3310`, `OAI.MUB6.Certificate.PairSemantics.sound3311`, `OAI.MUB6.Certificate.PairSemantics.sound3312`, `OAI.MUB6.Certificate.PairSemantics.sound3313`, `OAI.MUB6.Certificate.PairSemantics.sound3314`, `OAI.MUB6.Certificate.PairSemantics.sound3315`, `OAI.MUB6.Certificate.PairSemantics.sound3316`, `OAI.MUB6.Certificate.PairSemantics.sound3317`, `OAI.MUB6.Certificate.PairSemantics.sound3319`, `OAI.MUB6.Certificate.PairSemantics.sound3322`, `OAI.MUB6.Certificate.PairSemantics.sound3323`, `OAI.MUB6.Certificate.PairSemantics.sound3324`, `OAI.MUB6.Certificate.PairSemantics.sound3325`, `OAI.MUB6.Certificate.PairSemantics.sound3327`, `OAI.MUB6.Certificate.PairSemantics.sound3328`, `OAI.MUB6.Certificate.PairSemantics.sound3332`, `OAI.MUB6.Certificate.PairSemantics.sound3333`, `OAI.MUB6.Certificate.PairSemantics.sound3334`, `OAI.MUB6.Certificate.PairSemantics.sound3335`, `OAI.MUB6.Certificate.PairSemantics.sound3336`, `OAI.MUB6.Certificate.PairSemantics.sound3338`, `OAI.MUB6.Certificate.PairSemantics.sound3340`, `OAI.MUB6.Certificate.PairSemantics.sound3341`, `OAI.MUB6.Certificate.PairSemantics.sound3342`, `OAI.MUB6.Certificate.PairSemantics.sound3343`, `OAI.MUB6.Certificate.PairSemantics.sound3344`, `OAI.MUB6.Certificate.PairSemantics.sound3345`, `OAI.MUB6.Certificate.PairSemantics.sound3346`, `OAI.MUB6.Certificate.PairSemantics.sound3347`, `OAI.MUB6.Certificate.PairSemantics.sound3348`, `OAI.MUB6.Certificate.PairSemantics.sound3349`, `OAI.MUB6.Certificate.PairSemantics.sound3350`, `OAI.MUB6.Certificate.PairSemantics.sound3351`, `OAI.MUB6.Certificate.PairSemantics.sound3352`, `OAI.MUB6.Certificate.PairSemantics.sound3353`, `OAI.MUB6.Certificate.PairSemantics.sound3354`, `OAI.MUB6.Certificate.PairSemantics.sound3355`, `OAI.MUB6.Certificate.PairSemantics.sound3356`, `OAI.MUB6.Certificate.PairSemantics.sound3357`, `OAI.MUB6.Certificate.PairSemantics.sound3359`, `OAI.MUB6.Certificate.PairSemantics.sound3360`, `OAI.MUB6.Certificate.PairSemantics.sound3361`, `OAI.MUB6.Certificate.PairSemantics.sound3362`, `OAI.MUB6.Certificate.PairSemantics.sound3364`, `OAI.MUB6.Certificate.PairSemantics.sound3365`, `OAI.MUB6.Certificate.PairSemantics.sound3366`, `OAI.MUB6.Certificate.PairSemantics.sound3367`, `OAI.MUB6.Certificate.PairSemantics.sound3369`, `OAI.MUB6.Certificate.PairSemantics.sound3370`, `OAI.MUB6.Certificate.PairSemantics.sound3371`, `OAI.MUB6.Certificate.PairSemantics.sound3372`, `OAI.MUB6.Certificate.PairSemantics.sound3373`, `OAI.MUB6.Certificate.PairSemantics.sound3375`, `OAI.MUB6.Certificate.PairSemantics.sound3376`, `OAI.MUB6.Certificate.PairSemantics.sound3377`, `OAI.MUB6.Certificate.PairSemantics.sound3378`, `OAI.MUB6.Certificate.PairSemantics.sound3380`, `OAI.MUB6.Certificate.PairSemantics.sound3381`, `OAI.MUB6.Certificate.PairSemantics.sound3382`, `OAI.MUB6.Certificate.PairSemantics.sound3383`, `OAI.MUB6.Certificate.PairSemantics.sound3384`, `OAI.MUB6.Certificate.PairSemantics.sound3385`, `OAI.MUB6.Certificate.PairSemantics.sound3388`, `OAI.MUB6.Certificate.PairSemantics.sound3390`, `OAI.MUB6.Certificate.PairSemantics.sound3391`, `OAI.MUB6.Certificate.PairSemantics.sound3392`, `OAI.MUB6.Certificate.PairSemantics.sound3393`, `OAI.MUB6.Certificate.PairSemantics.sound3394`, `OAI.MUB6.Certificate.PairSemantics.sound3395`, `OAI.MUB6.Certificate.PairSemantics.sound3396`, `OAI.MUB6.Certificate.PairSemantics.sound3399`, `OAI.MUB6.Certificate.PairSemantics.sound3400`, `OAI.MUB6.Certificate.PairSemantics.sound3401`, `OAI.MUB6.Certificate.PairSemantics.sound3402`, `OAI.MUB6.Certificate.PairSemantics.sound3405`, `OAI.MUB6.Certificate.PairSemantics.sound3407`, `OAI.MUB6.Certificate.PairSemantics.sound3408`, `OAI.MUB6.Certificate.PairSemantics.sound3411`, `OAI.MUB6.Certificate.PairSemantics.sound3412`, `OAI.MUB6.Certificate.PairSemantics.sound3413`, `OAI.MUB6.Certificate.PairSemantics.sound3414`, `OAI.MUB6.Certificate.PairSemantics.sound3415`, `OAI.MUB6.Certificate.PairSemantics.sound3416`, `OAI.MUB6.Certificate.PairSemantics.sound3417`, `OAI.MUB6.Certificate.PairSemantics.sound3418`, `OAI.MUB6.Certificate.PairSemantics.sound3420`, `OAI.MUB6.Certificate.PairSemantics.sound3421`, `OAI.MUB6.Certificate.PairSemantics.sound3422`, `OAI.MUB6.Certificate.PairSemantics.sound3423`, `OAI.MUB6.Certificate.PairSemantics.sound3424`, `OAI.MUB6.Certificate.PairSemantics.sound3425`, `OAI.MUB6.Certificate.PairSemantics.sound3426`, `OAI.MUB6.Certificate.PairSemantics.sound3428`, `OAI.MUB6.Certificate.PairSemantics.sound3431`, `OAI.MUB6.Certificate.PairSemantics.sound3433`, `OAI.MUB6.Certificate.PairSemantics.sound3434`, `OAI.MUB6.Certificate.PairSemantics.sound3435`, `OAI.MUB6.Certificate.PairSemantics.sound3436`, `OAI.MUB6.Certificate.PairSemantics.sound3437`, `OAI.MUB6.Certificate.PairSemantics.sound3438`, `OAI.MUB6.Certificate.PairSemantics.sound3439`, `OAI.MUB6.Certificate.PairSemantics.sound3440`, `OAI.MUB6.Certificate.PairSemantics.sound3441`, `OAI.MUB6.Certificate.PairSemantics.sound3445`, `OAI.MUB6.Certificate.PairSemantics.sound3447`, `OAI.MUB6.Certificate.PairSemantics.sound3449`, `OAI.MUB6.Certificate.PairSemantics.sound3454`, `OAI.MUB6.Certificate.PairSemantics.sound3456`, `OAI.MUB6.Certificate.PairSemantics.sound3457`, `OAI.MUB6.Certificate.PairSemantics.sound3458`, `OAI.MUB6.Certificate.PairSemantics.sound3459`, `OAI.MUB6.Certificate.PairSemantics.sound3460`, `OAI.MUB6.Certificate.PairSemantics.sound3461`, `OAI.MUB6.Certificate.PairSemantics.sound3462`, `OAI.MUB6.Certificate.PairSemantics.sound3463`, `OAI.MUB6.Certificate.PairSemantics.sound3467`, `OAI.MUB6.Certificate.PairSemantics.sound3468`, `OAI.MUB6.Certificate.PairSemantics.sound381`, `OAI.MUB6.Certificate.PairSemantics.sound46`, `OAI.MUB6.Certificate.PairSemantics.sound545`, `OAI.MUB6.Certificate.PairSemantics.sound65`, `OAI.MUB6.Certificate.PairSemantics.sound659`, `OAI.MUB6.Certificate.PairSemantics.sound711`, `OAI.MUB6.Certificate.PairSemantics.sound856`, `OAI.MUB6.Certificate.PairSemantics.sound858`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound126`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound13`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound169`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound173`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound201`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound25`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound57`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99`, `OAI.MUB6.Certificate.PairTargetSemantics.certificate_zero1`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity0`, `OAI.MUB6.Certificate.PairTargetSemantics.partition12`, `OAI.MUB6.Certificate.PairTargetSemantics.partition14`, `OAI.MUB6.Certificate.PairTargetSemantics.partition16`, `OAI.MUB6.Certificate.PairTargetSemantics.partition19`, `OAI.MUB6.Certificate.PairTargetSemantics.partition24`, `OAI.MUB6.Certificate.PairTargetSemantics.partition25`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm1`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm10`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm15`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm20`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2 : Sparse (Fin 909) := [(6, (1 / 1))]

def value3 : Sparse (Fin 909) := [(2, (1 / 1))]

def value11 : Sparse (Fin 909) := [(0, (1 / 20)), (1, (-1 / 4))]

def value12 : Sparse (Fin 909) := [(2, (1 / 12)), (6, (1 / 6)), (9, (-1 / 3)), (58, (1 / 12))]

def value13 : Sparse (Fin 909) := [(5, (-1 / 3)), (9, (-2 / 3))]

def value14 : Sparse (Fin 909) := [(2, (1 / 12)), (6, (-1 / 6)), (58, (1 / 12))]

def value15 : Sparse (Fin 909) := [(2, (1 / 12)), (5, (-1 / 3)), (6, (1 / 12)), (9, (-1 / 3))]

def value16 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (1 / 6)), (5, (-1 / 3)), (6, (1 / 12))]

def value17 : Sparse (Fin 909) := [(257, (1 / 1))]

def value18 : Sparse (Fin 909) := [(60, (1 / 1))]

def value19 : Sparse (Fin 909) := [(32, (1 / 1))]

def value20 : Sparse (Fin 909) := [(67, (1 / 1))]

def value21 : Sparse (Fin 909) := [(34, (1 / 1))]

def value22 : Sparse (Fin 909) := [(276, (1 / 1))]

def value23 : Sparse (Fin 909) := [(68, (1 / 1))]

def value24 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (-1 / 6)), (6, (1 / 12))]

def value25 : Sparse (Fin 909) := [(1, (1 / 6)), (2, (1 / 6)), (5, (-1 / 3))]

def value26 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 4)), (2, (1 / 6))]

def value27 : Sparse (Fin 909) := [(69, (1 / 1))]

def value28 : Sparse (Fin 909) := [(70, (1 / 1))]

def value29 : Sparse (Fin 909) := [(278, (1 / 1))]

def value30 : Sparse (Fin 909) := [(71, (1 / 1))]

def value31 : Sparse (Fin 909) := [(7, (1 / 1))]

def value32 : Sparse (Fin 909) := [(35, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value128 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (-1 / 48)), (9, (1 / 12)), (70, (-1 / 3)), (71, (-1 / 3))]

def value129 : Sparse (Fin 909) := [(2, (1 / 24)), (6, (-1 / 24)), (9, (1 / 12)), (70, (-1 / 3))]

def value130 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 24)), (9, (1 / 12)), (58, (-1 / 48)), (278, (-1 / 3))]

def value131 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 6)), (6, (-1 / 24))]

def value132 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (35, (-1 / 3)), (52, (-1 / 3))]

def value133 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (82, (-1 / 3)), (128, (-1 / 3))]

def value134 : Sparse (Fin 909) := [(81, (1 / 1))]

def value135 : Sparse (Fin 909) := [(306, (1 / 1))]

def value136 : Sparse (Fin 909) := [(307, (1 / 1))]

def value137 : Sparse (Fin 909) := [(11, (-1 / 3)), (35, (-1 / 3)), (276, (-1 / 3))]

def value138 : Sparse (Fin 909) := [(35, (-1 / 3)), (82, (-1 / 3)), (276, (-1 / 3))]

def value139 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (-1 / 6)), (9, (1 / 12))]

def value140 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (7, (-1 / 3)), (69, (-1 / 3))]

def value141 : Sparse (Fin 909) := [(7, (-1 / 3)), (35, (-1 / 3)), (70, (-1 / 3))]

def value142 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 24)), (9, (1 / 12)), (58, (-1 / 48)), (310, (-1 / 3))]

def value143 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 16)), (5, (1 / 6)), (6, (-1 / 24)), (9, (1 / 12))]

def value144 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (8, (-1 / 3)), (71, (-1 / 3))]

def value145 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 24)), (5, (1 / 12)), (7, (-1 / 3))]

def value146 : Sparse (Fin 909) := [(3, (-1 / 3)), (7, (-1 / 3)), (35, (-1 / 3))]

def value147 : Sparse (Fin 909) := [(13, (-1 / 3)), (35, (-1 / 3)), (82, (-1 / 3))]

def value148 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (52, (-1 / 3)), (310, (-1 / 3))]

def value149 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-1 / 12)), (5, (1 / 6)), (6, (-1 / 48))]

def value150 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-1 / 24)), (5, (1 / 12)), (8, (-1 / 3))]

def value151 : Sparse (Fin 909) := [(10, (1 / 1))]

def value152 : Sparse (Fin 909) := [(308, (1 / 1))]

def value153 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (7, (-1 / 3)), (8, (-1 / 3))]

def value154 : Sparse (Fin 909) := [(309, (1 / 1))]

def value155 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 24)), (5, (1 / 12)), (6, (-1 / 48)), (35, (-1 / 3))]

def value156 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (82, (-1 / 3)), (310, (-1 / 3))]

def value157 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 12)), (6, (1 / 24)), (82, (-1 / 3))]

def value158 : Sparse (Fin 909) := [(52, (-1 / 3)), (60, (-1 / 3)), (128, (-1 / 3))]

def value159 : Sparse (Fin 909) := [(123, (1 / 1))]

def value160 : Sparse (Fin 909) := [(489, (1 / 1))]

def value161 : Sparse (Fin 909) := [(490, (1 / 1))]

def value162 : Sparse (Fin 909) := [(124, (1 / 1))]

def value163 : Sparse (Fin 909) := [(125, (1 / 1))]

def value164 : Sparse (Fin 909) := [(492, (1 / 1))]

def value165 : Sparse (Fin 909) := [(5, (1 / 12)), (9, (1 / 12)), (69, (-1 / 3)), (495, (-1 / 3))]

def value166 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (52, (-1 / 3)), (69, (-1 / 3))]

def value167 : Sparse (Fin 909) := [(126, (1 / 1))]

def value168 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (1 / 24)), (5, (1 / 12))]

def value169 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-1 / 48)), (3, (-1 / 3)), (7, (-1 / 3))]

def value170 : Sparse (Fin 909) := [(3, (-1 / 3)), (13, (-1 / 3)), (35, (-1 / 3))]

def value171 : Sparse (Fin 909) := [(13, (-1 / 3)), (82, (-1 / 3)), (128, (-1 / 3))]

def value172 : Sparse (Fin 909) := [(52, (-1 / 3)), (310, (-1 / 3)), (495, (-1 / 3))]

def value173 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 16)), (5, (1 / 12)), (6, (-1 / 48)), (52, (-1 / 3))]

def value174 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (2, (-1 / 12)), (5, (1 / 12))]

def value175 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 12)), (2, (-1 / 24)), (8, (-1 / 3))]

def value176 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 8)), (2, (-1 / 48)), (3, (-1 / 3))]

def value177 : Sparse (Fin 909) := [(3, (-1 / 3)), (12, (-1 / 3)), (13, (-1 / 3))]

def value178 : Sparse (Fin 909) := [(13, (-2 / 3)), (128, (-1 / 3))]

def value179 : Sparse (Fin 909) := [(35, (-1 / 3)), (52, (-1 / 3)), (495, (-1 / 3))]

def value180 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (3, (-1 / 3)), (52, (-1 / 3))]

def value181 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 48)), (2, (-1 / 16))]

def value182 : Sparse (Fin 909) := [(127, (1 / 1))]

def value183 : Sparse (Fin 909) := [(493, (1 / 1))]

def value184 : Sparse (Fin 909) := [(51, (1 / 1))]

def value185 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 48)), (2, (-1 / 24)), (3, (-1 / 3))]

def value186 : Sparse (Fin 909) := [(494, (1 / 1))]

def value187 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (13, (-1 / 3)), (52, (-1 / 3))]

def value188 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (1 / 48)), (13, (-1 / 3))]

def value189 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (128, (-1 / 3)), (495, (-1 / 3))]

def value190 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (52, (-1 / 3)), (128, (-1 / 3))]

def value191 : Sparse (Fin 909) := [(721, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value192 : Sparse (Fin 909) := [(196, (1 / 1))]

def value193 : Sparse (Fin 909) := [(723, (1 / 1))]

def value194 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (-1 / 48)), (9, (1 / 12)), (70, (-1 / 3)), (278, (-1 / 3))]

def value195 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (-1 / 48)), (35, (-1 / 3)), (70, (-1 / 3))]

def value196 : Sparse (Fin 909) := [(197, (1 / 1))]

def value197 : Sparse (Fin 909) := [(23, (1 / 1))]

def value198 : Sparse (Fin 909) := [(54, (1 / 1))]

def value199 : Sparse (Fin 909) := [(199, (1 / 1))]

def value200 : Sparse (Fin 909) := [(726, (1 / 1))]

def value201 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (7, (-1 / 3)), (35, (-1 / 3))]

def value202 : Sparse (Fin 909) := [(24, (1 / 1))]

def value203 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 16)), (3, (-1 / 3)), (12, (-1 / 3))]

def value204 : Sparse (Fin 909) := [(12, (-1 / 3)), (13, (-2 / 3))]

def value205 : Sparse (Fin 909) := [(35, (-1 / 3)), (278, (-1 / 3)), (495, (-1 / 3))]

def value206 : Sparse (Fin 909) := [(3, (-1 / 3)), (35, (-1 / 3)), (52, (-1 / 3))]

def value207 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 8)), (12, (-1 / 3))]

def value208 : Sparse (Fin 909) := [(11, (-1 / 3)), (35, (-1 / 3)), (278, (-1 / 3))]

def value209 : Sparse (Fin 909) := [(3, (-1 / 3)), (26, (-1 / 3)), (35, (-1 / 3))]

def value210 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 16)), (3, (-1 / 3)), (4, (-1 / 3))]

def value211 : Sparse (Fin 909) := [(727, (1 / 1))]

def value212 : Sparse (Fin 909) := [(55, (1 / 1))]

def value213 : Sparse (Fin 909) := [(728, (1 / 1))]

def value214 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 16)), (13, (-1 / 3)), (35, (-1 / 3))]

def value215 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (3, (-1 / 3)), (13, (-1 / 3))]

def value216 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 16)), (82, (-1 / 3)), (278, (-1 / 3))]

def value217 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (35, (-1 / 3)), (82, (-1 / 3))]

def value218 : Sparse (Fin 909) := [(201, (1 / 1))]

def value219 : Sparse (Fin 909) := [(796, (1 / 1))]

def value220 : Sparse (Fin 909) := [(226, (1 / 1))]

def value221 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (-1 / 48)), (11, (-1 / 3)), (35, (-1 / 3))]

def value222 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 16)), (26, (-1 / 3)), (35, (-1 / 3))]

def value223 : Sparse (Fin 909) := [(56, (1 / 1))]

def value224 : Sparse (Fin 909) := [(25, (1 / 1))]

def value225 : Sparse (Fin 909) := [(228, (1 / 1))]

def value226 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-1 / 48)), (3, (-1 / 3)), (26, (-1 / 3))]

def value227 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 24))]

def value228 : Sparse (Fin 909) := [(11, (-1 / 3)), (26, (-1 / 3)), (35, (-1 / 3))]

def value229 : Sparse (Fin 909) := [(3, (-1 / 3)), (4, (-1 / 3)), (26, (-1 / 3))]

def value230 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 24)), (4, (-1 / 3))]

def value231 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (1 / 12)), (2, (-1 / 6)), (5, (1 / 6)), (27, (-1 / 2))]

def value232 : Sparse (Fin 909) := [(0, (-1 / 15)), (1, (1 / 4)), (2, (-1 / 12))]

def value233 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 6)), (6, (-1 / 48)), (9, (1 / 12)), (310, (-1 / 3))]

def value234 : Sparse (Fin 909) := [(818, (1 / 1))]

def value235 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 24)), (9, (1 / 12)), (495, (-1 / 3))]

def value236 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 8)), (58, (-1 / 48)), (278, (-1 / 3))]

def value237 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 16)), (5, (1 / 12)), (6, (-1 / 16)), (9, (1 / 12)), (58, (-1 / 48))]

def value238 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 24)), (5, (1 / 6)), (6, (-1 / 48)), (9, (1 / 6))]

def value239 : Sparse (Fin 909) := [(2, (1 / 24)), (6, (1 / 48)), (9, (1 / 12)), (58, (-1 / 48))]

def value240 : Sparse (Fin 909) := [(5, (-1 / 6)), (9, (1 / 6))]

def value241 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 16)), (5, (1 / 12)), (6, (-1 / 48)), (71, (-1 / 3))]

def value242 : Sparse (Fin 909) := [(2, (1 / 24)), (5, (1 / 12)), (6, (1 / 8))]

def value243 : Sparse (Fin 909) := [(1, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 24))]

def value244 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (5, (1 / 6)), (8, (-1 / 3))]

def value245 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 16)), (5, (1 / 12)), (6, (-1 / 24)), (52, (-1 / 3))]

def value246 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-1 / 16)), (5, (1 / 12)), (52, (-1 / 3))]

def value247 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 24)), (5, (1 / 6)), (6, (-1 / 48)), (35, (-1 / 3))]

def value248 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 8)), (6, (-1 / 48)), (35, (-1 / 3))]

def value249 : Sparse (Fin 909) := [(2, (1 / 24)), (6, (1 / 24)), (11, (-1 / 3))]

def value250 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 16)), (5, (1 / 6)), (6, (-1 / 48)), (9, (1 / 12))]

def value251 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (5, (1 / 12)), (6, (-1 / 24)), (9, (1 / 12))]

def value252 : Sparse (Fin 909) := [(2, (1 / 24)), (6, (5 / 48)), (58, (-1 / 48))]

def value253 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 12)), (2, (-1 / 12)), (5, (1 / 12)), (6, (-1 / 48))]

def value254 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 48)), (5, (1 / 12)), (6, (-1 / 48))]

def value255 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (5 / 48)), (6, (1 / 24))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value105 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (13, (-2 / 3))]

def value106 : Sparse (Fin 909) := [(26, (-1 / 3)), (35, (-1 / 3)), (67, (-1 / 3))]

def value107 : Sparse (Fin 909) := [(3, (-1 / 3)), (13, (-1 / 3)), (34, (-1 / 3))]

def value108 : Sparse (Fin 909) := [(26, (-1 / 3)), (34, (-1 / 3)), (67, (-1 / 3))]

def value109 : Sparse (Fin 909) := [(3, (-1 / 3)), (26, (-1 / 3)), (34, (-1 / 3))]

def value111 : Sparse (Fin 909) := [(33, (1 / 1))]

def value112 : Sparse (Fin 909) := [(273, (1 / 1))]

def value113 : Sparse (Fin 909) := [(35, (-1 / 3)), (67, (-1 / 3)), (276, (-1 / 3))]

def value114 : Sparse (Fin 909) := [(66, (1 / 1))]

def value115 : Sparse (Fin 909) := [(275, (1 / 1))]

def value116 : Sparse (Fin 909) := [(1, (-1 / 8)), (2, (-1 / 24)), (5, (1 / 3)), (6, (-1 / 12)), (9, (1 / 6)), (68, (-1 / 2))]

def value117 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 12)), (5, (1 / 6)), (27, (-1 / 2)), (68, (-1 / 1))]

def value118 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 12)), (2, (1 / 12)), (5, (1 / 6)), (6, (-1 / 24))]

def value119 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 6)), (9, (1 / 12)), (69, (-1 / 3))]

def value120 : Sparse (Fin 909) := [(7, (-1 / 3)), (69, (-1 / 3)), (70, (-1 / 3))]

def value121 : Sparse (Fin 909) := [(35, (-1 / 3)), (70, (-1 / 3)), (278, (-1 / 3))]

def value122 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 16)), (9, (1 / 6)), (58, (-1 / 48))]

def value123 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 48)), (9, (1 / 12)), (71, (-1 / 3))]

def value124 : Sparse (Fin 909) := [(8, (-1 / 3)), (71, (-2 / 3))]

def value125 : Sparse (Fin 909) := [(277, (1 / 1))]

def value126 : Sparse (Fin 909) := [(5, (1 / 12)), (9, (1 / 12)), (69, (-1 / 3)), (71, (-1 / 3))]

def value127 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 12)), (69, (-1 / 3)), (71, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value256 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (5, (-1 / 6))]

def value257 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (9, (1 / 12)), (68, (-1 / 4))]

def value258 : Sparse (Fin 909) := [(236, (1 / 1))]

def value259 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (5 / 48))]

def value260 : Sparse (Fin 909) := [(237, (1 / 1))]

def value261 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 12)), (2, (-1 / 16)), (3, (-1 / 3))]

def value262 : Sparse (Fin 909) := [(238, (1 / 1))]

def value263 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (26, (-1 / 3))]

def value264 : Sparse (Fin 909) := [(27, (-1 / 4)), (68, (-1 / 4))]

def value265 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (5, (1 / 12)), (68, (-1 / 4))]

def value266 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (-1 / 6)), (6, (-1 / 48)), (9, (1 / 12))]

def value267 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 48)), (2, (1 / 48)), (6, (-1 / 48))]

def value268 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (-1 / 16)), (5, (1 / 12))]

def value269 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 48)), (6, (-1 / 48))]

def value270 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (5, (1 / 12)), (6, (1 / 24))]

def value271 : Sparse (Fin 909) := [(0, (-1 / 120)), (2, (-1 / 24))]

def value272 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 48)), (2, (1 / 24))]

def value273 : Sparse (Fin 909) := [(1, (-1 / 16)), (5, (1 / 12)), (6, (-1 / 48))]

def value274 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (5, (1 / 12)), (27, (-1 / 4))]

def value275 : Sparse (Fin 909) := [(30, (1 / 1))]

def value276 : Sparse (Fin 909) := [(31, (1 / 1))]

def value277 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 24)), (6, (-1 / 48)), (68, (-1 / 4))]

def value278 : Sparse (Fin 909) := [(2, (1 / 24)), (5, (1 / 12)), (6, (1 / 24)), (9, (1 / 12))]

def value279 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 24)), (2, (-1 / 48)), (27, (-1 / 4))]

def value280 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (1 / 12))]

def value281 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 24)), (5, (-1 / 6)), (6, (-1 / 48))]

def value282 : Sparse (Fin 909) := [(5, (1 / 6)), (9, (1 / 3))]

def value283 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 48)), (2, (-1 / 48))]

def value284 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 48)), (2, (-1 / 48))]

def value285 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 48))]

def value286 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 12)), (5, (1 / 6)), (6, (-1 / 24))]

def value287 : Sparse (Fin 909) := [(0, (-1 / 24)), (1, (1 / 24))]

def value288 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 12)), (2, (-1 / 24))]

def value289 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 24)), (6, (-1 / 48))]

def value290 : Sparse (Fin 909) := [(2, (1 / 8)), (6, (1 / 8))]

def value291 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 24)), (2, (-1 / 48))]

def value292 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (1 / 8))]

def value293 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 48))]

def value294 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 8))]

def value295 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 12)), (2, (5 / 6)), (5, (-5 / 2)), (6, (5 / 8)), (9, (-10 / 3)), (58, (1 / 6))]

def value296 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 24)), (2, (-1 / 24)), (9, (-5 / 6)), (58, (1 / 24))]

def value297 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 6)), (6, (1 / 24)), (9, (-1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (71, (1 / 3))]

def value298 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 12)), (52, (1 / 3)), (69, (1 / 3)), (71, (1 / 6)), (256, (-1 / 2)), (495, (1 / 6))]

def value299 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 3)), (35, (1 / 6)), (69, (1 / 2)), (70, (1 / 2)), (71, (1 / 6)), (257, (1 / 6))]

def value300 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (256, (-1 / 2)), (257, (1 / 6)), (495, (1 / 6))]

def value301 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (5 / 96)), (5, (-1 / 6)), (6, (1 / 48)), (9, (-1 / 8)), (52, (1 / 6)), (69, (1 / 3)), (71, (1 / 3)), (495, (1 / 6))]

def value302 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 3)), (69, (1 / 3)), (71, (1 / 1))]

def value303 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 6)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 2)), (256, (-1 / 2))]

def value304 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 96)), (5, (-1 / 12)), (6, (1 / 48)), (9, (-1 / 12)), (35, (1 / 3)), (69, (1 / 6)), (70, (1 / 6)), (257, (1 / 3)), (495, (1 / 3))]

def value305 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 16)), (6, (1 / 96)), (13, (1 / 6)), (60, (1 / 6)), (70, (1 / 6)), (257, (1 / 6))]

def value306 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 96)), (5, (-1 / 24)), (6, (1 / 96)), (9, (-1 / 8)), (35, (1 / 6)), (495, (1 / 6))]

def value307 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 24)), (13, (1 / 6)), (69, (1 / 6)), (128, (1 / 6)), (495, (1 / 6))]

def value308 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (35, (1 / 6)), (52, (1 / 3)), (59, (-1 / 2)), (256, (-1 / 2))]

def value309 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (60, (1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (257, (1 / 6)), (260, (-1 / 2))]

def value310 : Sparse (Fin 909) := [(3, (1 / 6)), (13, (1 / 6)), (35, (1 / 2)), (52, (1 / 3)), (60, (1 / 3)), (128, (1 / 6)), (257, (1 / 6)), (495, (1 / 6))]

def value311 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 16)), (5, (-1 / 6)), (6, (1 / 24)), (9, (-1 / 12)), (52, (1 / 3)), (128, (1 / 3)), (495, (1 / 3))]

def value312 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-7 / 96)), (6, (1 / 96)), (13, (1 / 2)), (35, (1 / 2)), (60, (1 / 3))]

def value313 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 48)), (5, (-1 / 12)), (6, (1 / 32)), (26, (1 / 6)), (35, (1 / 3)), (259, (-1 / 2)), (495, (1 / 6))]

def value314 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (13, (1 / 3)), (52, (1 / 3)), (59, (-1 / 2)), (128, (1 / 6))]

def value315 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 6)), (54, (-1 / 2)), (259, (-1 / 2)), (260, (-1 / 2))]

def value316 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (3, (1 / 3)), (5, (-1 / 24)), (7, (1 / 6)), (13, (1 / 6)), (35, (1 / 2)), (52, (1 / 3)), (60, (1 / 6))]

def value317 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (1 / 2)), (35, (1 / 6)), (52, (1 / 6)), (59, (-1 / 2)), (60, (1 / 6)), (128, (1 / 6))]

def value318 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 3)), (128, (1 / 6)), (262, (-1 / 2)), (495, (1 / 6))]

def value319 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (56, (-1 / 2)), (262, (-1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1006 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-7 / 144)), (3, (1 / 9)), (4, (2 / 9))]

def value1007 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 48)), (33, (-1 / 3)), (51, (-1 / 3))]

def value1008 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1009 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (-1 / 9))]

def value1010 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9)), (25, (-1 / 3))]

def value1011 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (64, (-1 / 3))]

def value1012 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-5 / 144)), (63, (-1 / 3)), (237, (-1 / 3))]

def value1013 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (1 / 24)), (3, (1 / 9)), (33, (-1 / 3))]

def value1014 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (306, (-1 / 3)), (308, (-1 / 3))]

def value1015 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (13, (2 / 9)), (52, (1 / 9))]

def value1016 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (33, (-1 / 3))]

def value1017 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (55, (-1 / 3)), (63, (-1 / 3))]

def value1018 : Sparse (Fin 909) := [(3, (1 / 3)), (13, (1 / 9)), (26, (2 / 9)), (34, (1 / 3))]

def value1019 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 36)), (52, (1 / 9)), (721, (-1 / 3))]

def value1020 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (721, (-1 / 3))]

def value1021 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 18)), (6, (1 / 72)), (68, (1 / 12)), (196, (-1 / 3))]

def value1022 : Sparse (Fin 909) := [(2, (-1 / 18)), (5, (-1 / 36)), (6, (-1 / 18)), (9, (-1 / 36)), (723, (-1 / 3))]

def value1023 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 144)), (5, (-1 / 36)), (9, (-1 / 36)), (35, (1 / 9)), (70, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1024 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (68, (1 / 12)), (197, (-1 / 3))]

def value1025 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (196, (-1 / 3)), (728, (-1 / 3))]

def value1026 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (2 / 9)), (70, (1 / 9)), (309, (-1 / 3))]

def value1027 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 18)), (2, (1 / 72)), (23, (-1 / 3)), (27, (1 / 12))]

def value1028 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-7 / 144)), (5, (-1 / 36)), (54, (-1 / 3))]

def value1029 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (1 / 9)), (6, (1 / 72)), (199, (-1 / 3))]

def value1030 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (9, (-1 / 9)), (726, (-1 / 3))]

def value1031 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 48)), (5, (1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9))]

def value1032 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9))]

def value1033 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (1 / 72)), (24, (-1 / 3)), (27, (1 / 12))]

def value1034 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (199, (-1 / 3)), (726, (-1 / 3))]

def value1035 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (54, (-1 / 3)), (228, (-1 / 3))]

def value1036 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (2 / 9)), (7, (1 / 9)), (51, (-1 / 3))]

def value1037 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (7, (-1 / 9)), (8, (1 / 9))]

def value1038 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (69, (1 / 3)), (70, (1 / 9)), (71, (2 / 9))]

def value1039 : Sparse (Fin 909) := [(1, (5 / 72)), (2, (1 / 72))]

def value1040 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-7 / 72)), (2, (1 / 144)), (3, (1 / 9)), (12, (1 / 9))]

def value1041 : Sparse (Fin 909) := [(0, (-1 / 360)), (2, (-1 / 72)), (12, (1 / 9)), (13, (2 / 9))]

def value1042 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (35, (1 / 9)), (52, (1 / 9))]

def value1043 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-7 / 144)), (2, (1 / 144)), (3, (1 / 9))]

def value1044 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 16)), (2, (1 / 72))]

def value1045 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (-5 / 72)), (12, (1 / 9))]

def value1046 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9))]

def value1047 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 16)), (2, (1 / 72)), (3, (1 / 9)), (4, (1 / 9))]

def value1048 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-1 / 18))]

def value1049 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 48)), (2, (5 / 144)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (52, (1 / 9))]

def value1050 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value1051 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (1 / 36)), (6, (1 / 144)), (9, (-1 / 36)), (68, (1 / 12)), (727, (-1 / 3))]

def value1052 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (5, (-1 / 36)), (27, (1 / 12)), (55, (-1 / 3))]

def value1053 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9))]

def value1054 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 48)), (12, (1 / 9))]

def value1055 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 3)), (308, (-1 / 3))]

def value1056 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3))]

def value1057 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 9)), (12, (-1 / 9))]

def value1058 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (4, (2 / 9)), (12, (1 / 9))]

def value1059 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 3))]

def value1060 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (52, (1 / 9)), (69, (1 / 9)), (125, (-1 / 3)), (126, (-1 / 3))]

def value1061 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 36)), (5, (-1 / 36)), (6, (-1 / 144)), (9, (-1 / 36)), (68, (1 / 12)), (728, (-1 / 3))]

def value1062 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 24)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9))]

def value1063 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (-5 / 144)), (3, (1 / 9)), (13, (1 / 9))]

def value1064 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (2 / 9)), (82, (1 / 9)), (309, (-1 / 3))]

def value1065 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (13, (-1 / 9)), (52, (1 / 9))]

def value1066 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (2 / 9)), (12, (1 / 9)), (13, (4 / 9))]

def value1067 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value1068 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (35, (1 / 9)), (70, (1 / 9)), (196, (-1 / 3)), (197, (-1 / 3))]

def value1069 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 36)), (6, (-1 / 36)), (35, (1 / 9)), (82, (1 / 9))]

def value1070 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (201, (-1 / 3))]

def value1071 : Sparse (Fin 909) := [(2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 72)), (13, (1 / 9)), (52, (2 / 9)), (82, (1 / 9)), (128, (1 / 3))]

def value1072 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-5 / 144)), (5, (-1 / 36)), (6, (1 / 72)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value1073 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (55, (-1 / 3)), (237, (-1 / 3))]

def value1074 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (2 / 9)), (35, (1 / 9)), (238, (-1 / 3))]

def value1075 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (35, (-1 / 9))]

def value1076 : Sparse (Fin 909) := [(7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (2 / 9)), (307, (-1 / 3))]

def value1077 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (8, (1 / 9)), (201, (-1 / 3)), (818, (-1 / 3))]

def value1078 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (2 / 9)), (31, (-1 / 3))]

def value1079 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (3, (-1 / 9))]

def value1080 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 18)), (35, (1 / 9)), (52, (1 / 3))]

def value1081 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 144)), (2, (1 / 18)), (3, (1 / 9))]

def value1082 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 48)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value1083 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value1084 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (24, (-1 / 3)), (30, (-1 / 3))]

def value1085 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (71, (1 / 9)), (197, (-1 / 3)), (236, (-1 / 3))]

def value1086 : Sparse (Fin 909) := [(13, (2 / 9)), (35, (2 / 9)), (60, (2 / 9)), (490, (-1 / 3))]

def value1087 : Sparse (Fin 909) := [(13, (1 / 9)), (52, (1 / 9)), (59, (-2 / 3)), (128, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1088 : Sparse (Fin 909) := [(28, (1 / 1))]

def value1089 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 12)), (6, (1 / 144)), (35, (1 / 9)), (52, (1 / 9)), (306, (-1 / 3))]

def value1090 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (2 / 9)), (35, (2 / 9)), (67, (1 / 9)), (273, (-1 / 3))]

def value1091 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (52, (2 / 9)), (69, (1 / 9)), (262, (-1 / 3))]

def value1092 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-7 / 144)), (5, (-1 / 36)), (123, (-1 / 3))]

def value1093 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (2 / 9)), (35, (1 / 9)), (123, (-1 / 3))]

def value1094 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9))]

def value1095 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (35, (1 / 9)), (52, (1 / 9))]

def value1096 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-11 / 144)), (2, (1 / 144)), (31, (-1 / 3))]

def value1097 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9)), (490, (-1 / 3))]

def value1098 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9)), (33, (-1 / 3))]

def value1099 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (3, (1 / 9))]

def value1100 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (7, (1 / 9)), (8, (2 / 9)), (81, (-1 / 3))]

def value1101 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (5 / 36)), (6, (1 / 72)), (226, (-1 / 3))]

def value1102 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (6, (-1 / 36)), (11, (1 / 9)), (35, (1 / 9))]

def value1103 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (1 / 144)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9))]

def value1104 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (56, (-1 / 3))]

def value1105 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (13, (1 / 3)), (35, (1 / 9)), (52, (1 / 9))]

def value1106 : Sparse (Fin 909) := [(13, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (60, (1 / 3)), (128, (1 / 9))]

def value1107 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 36)), (2, (1 / 72)), (25, (-1 / 3))]

def value1108 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (1 / 36)), (6, (1 / 144)), (228, (-1 / 3))]

def value1109 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (3, (1 / 9)), (26, (1 / 9))]

def value1110 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9))]

def value1111 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (25, (-1 / 3)), (26, (1 / 9))]

def value1112 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 12)), (3, (2 / 9)), (12, (1 / 3))]

def value1113 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 18)), (7, (1 / 3)), (8, (1 / 9)), (35, (1 / 9))]

def value1114 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-1 / 18))]

def value1115 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 24)), (5, (-1 / 36)), (6, (-1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value1116 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value1117 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 144)), (4, (1 / 9))]

def value1118 : Sparse (Fin 909) := [(0, (-19 / 720)), (1, (-1 / 144))]

def value1119 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-7 / 72)), (4, (1 / 9))]

def value1120 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (35, (1 / 9)), (54, (-1 / 3))]

def value1121 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (11, (1 / 9)), (26, (1 / 9)), (35, (1 / 3))]

def value1122 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (-1 / 144)), (3, (1 / 9)), (26, (1 / 9))]

def value1123 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 9)), (26, (1 / 9))]

def value1124 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 36)), (26, (-1 / 9))]

def value1125 : Sparse (Fin 909) := [(7, (1 / 9)), (26, (2 / 9)), (35, (1 / 3)), (67, (1 / 3))]

def value1126 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 36)), (4, (-1 / 9))]

def value1127 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (81, (-1 / 3))]

def value1128 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 144)), (5, (-1 / 18)), (6, (1 / 72)), (26, (1 / 9)), (35, (1 / 9))]

def value1129 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 36)), (5, (-1 / 18)), (8, (2 / 9)), (56, (-1 / 3))]

def value1130 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (1 / 48)), (2, (1 / 24)), (8, (1 / 6)), (30, (-1 / 2))]

def value1131 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (1 / 48)), (24, (-1 / 2)), (27, (1 / 4)), (30, (-1 / 2))]

def value1132 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (56, (-1 / 2))]

def value1133 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 24)), (201, (-1 / 2)), (818, (-1 / 2))]

def value1134 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 16)), (5, (1 / 12)), (6, (1 / 48)), (8, (1 / 6)), (201, (-1 / 2))]

def value1135 : Sparse (Fin 909) := [(0, (1 / 30)), (1, (-1 / 8)), (2, (1 / 24))]

def value1136 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 16)), (2, (1 / 32)), (27, (1 / 8)), (31, (-1 / 2)), (51, (-1 / 2))]

def value1137 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 48)), (68, (1 / 8)), (237, (-1 / 2)), (494, (-1 / 2))]

def value1138 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (13, (1 / 6)), (52, (1 / 6))]

def value1139 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 32)), (2, (-1 / 48)), (3, (1 / 6)), (13, (1 / 6))]

def value1140 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (5 / 48)), (5, (-1 / 12)), (6, (1 / 24)), (52, (1 / 3)), (128, (1 / 6))]

def value1141 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 12)), (2, (1 / 32)), (3, (1 / 6)), (4, (1 / 6)), (31, (-1 / 2))]

def value1142 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 12)), (2, (1 / 16)), (3, (1 / 3)), (12, (1 / 6))]

def value1143 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (55, (-1 / 2))]

def value1144 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 12)), (6, (-1 / 48)), (9, (-1 / 24)), (52, (1 / 6)), (728, (-1 / 2))]

def value1145 : Sparse (Fin 909) := [(5, (1 / 12)), (9, (-1 / 12))]

def value1146 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-1 / 12)), (2, (1 / 16)), (5, (-1 / 24)), (27, (1 / 8))]

def value1147 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (27, (1 / 8))]

def value1149 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 12)), (2, (-1 / 16)), (5, (-1 / 24)), (6, (1 / 96))]

def value1150 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value1151 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-1 / 12)), (2, (1 / 48))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1152 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 48))]

def value1153 : Sparse (Fin 909) := [(0, (1 / 30)), (1, (-1 / 8)), (2, (1 / 24))]

def value1154 : Sparse (Fin 909) := [(1, (1 / 72)), (5, (-1 / 36)), (6, (1 / 72)), (259, (-1 / 3)), (721, (-1 / 3))]

def value1155 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (59, (-1 / 3))]

def value1156 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (-1 / 9)), (128, (1 / 9))]

def value1157 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9)), (262, (-1 / 3))]

def value1158 : Sparse (Fin 909) := [(13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (60, (2 / 9)), (128, (1 / 9)), (260, (-1 / 3))]

def value1159 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (59, (-1 / 3)), (259, (-1 / 3))]

def value1160 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (-1 / 9)), (6, (1 / 72)), (9, (-1 / 9)), (818, (-1 / 3))]

def value1161 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (9, (-1 / 6))]

def value1162 : Sparse (Fin 909) := [(54, (-1 / 3)), (259, (-1 / 3)), (723, (-1 / 3))]

def value1163 : Sparse (Fin 909) := [(54, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 3))]

def value1164 : Sparse (Fin 909) := [(12, (1 / 9)), (13, (2 / 9)), (59, (-1 / 3)), (199, (-1 / 3))]

def value1165 : Sparse (Fin 909) := [(13, (-1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (2 / 9))]

def value1166 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (490, (-1 / 3)), (492, (-1 / 3))]

def value1167 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 12)), (5, (-1 / 36)), (6, (-1 / 36))]

def value1168 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (1 / 48)), (6, (1 / 144)), (8, (1 / 9))]

def value1169 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (13, (1 / 9)), (35, (2 / 9)), (82, (1 / 9))]

def value1170 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 36)), (5, (1 / 36)), (6, (1 / 144)), (52, (1 / 9))]

def value1171 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (52, (1 / 9))]

def value1172 : Sparse (Fin 909) := [(56, (-1 / 3)), (228, (-1 / 3)), (796, (-1 / 3))]

def value1173 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (2 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (201, (-1 / 3))]

def value1174 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-1 / 144)), (6, (-1 / 144)), (35, (1 / 9))]

def value1175 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (-1 / 9)), (82, (1 / 9))]

def value1176 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (7 / 144)), (5, (-1 / 12)), (6, (1 / 48))]

def value1177 : Sparse (Fin 909) := [(1, (-7 / 144)), (2, (-5 / 144)), (5, (1 / 36)), (6, (1 / 72))]

def value1178 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 72)), (5, (1 / 9)), (6, (1 / 144))]

def value1179 : Sparse (Fin 909) := [(54, (-1 / 3)), (228, (-1 / 3)), (492, (-1 / 3))]

def value1180 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (199, (-1 / 3))]

def value1181 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (13 / 144)), (6, (-1 / 18))]

def value1182 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-5 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (9, (-1 / 18)), (68, (1 / 12))]

def value1183 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (226, (-1 / 3)), (723, (-1 / 3))]

def value1184 : Sparse (Fin 909) := [(2, (-1 / 48)), (6, (1 / 144)), (35, (1 / 9)), (70, (1 / 9)), (196, (-1 / 3)), (723, (-1 / 3))]

def value1185 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 48)), (26, (1 / 9)), (35, (2 / 9)), (82, (1 / 9))]

def value1186 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (8, (1 / 9)), (56, (-1 / 3)), (201, (-1 / 3))]

def value1187 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (71, (1 / 9)), (197, (-1 / 3)), (796, (-1 / 3))]

def value1188 : Sparse (Fin 909) := [(25, (-1 / 3)), (123, (-1 / 3)), (226, (-1 / 3))]

def value1189 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (-1 / 9)), (52, (1 / 9))]

def value1190 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3)), (54, (-1 / 3))]

def value1191 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9))]

def value1192 : Sparse (Fin 909) := [(10, (-1 / 3)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9)), (306, (-1 / 3))]

def value1193 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (1 / 9)), (13, (-1 / 9)), (34, (1 / 9))]

def value1194 : Sparse (Fin 909) := [(10, (-1 / 3)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9)), (307, (-1 / 3))]

def value1195 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (6, (1 / 144)), (27, (1 / 12)), (68, (1 / 12)), (236, (-1 / 3))]

def value1196 : Sparse (Fin 909) := [(55, (-1 / 3)), (197, (-1 / 3)), (728, (-1 / 3))]

def value1197 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 16)), (5, (-1 / 36)), (6, (1 / 144))]

def value1198 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (5, (-1 / 36)), (8, (1 / 9))]

def value1199 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-5 / 72)), (5, (-1 / 36)), (6, (1 / 144))]

def value1200 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 144)), (3, (1 / 9)), (6, (1 / 144)), (11, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value1201 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 72)), (2, (1 / 24)), (6, (1 / 144))]

def value1202 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-11 / 144)), (2, (-1 / 48))]

def value1203 : Sparse (Fin 909) := [(1, (5 / 72)), (2, (1 / 72))]

def value1204 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (-1 / 72)), (3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (35, (1 / 9))]

def value1205 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (6, (1 / 144)), (27, (1 / 12)), (68, (1 / 12)), (237, (-1 / 3))]

def value1206 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36))]

def value1207 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (-1 / 144)), (3, (1 / 9))]

def value1208 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9)), (56, (-1 / 3))]

def value1209 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9))]

def value1210 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (5, (-1 / 18)), (68, (1 / 12)), (238, (-1 / 3))]

def value1211 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-5 / 72)), (6, (1 / 144)), (26, (1 / 9))]

def value1212 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 72)), (2, (5 / 144)), (26, (1 / 9))]

def value1213 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (27, (1 / 12)), (238, (-1 / 3))]

def value1214 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (1 / 9)), (26, (-1 / 9)), (35, (1 / 9))]

def value1215 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (55, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1216 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 144)), (2, (5 / 144)), (5, (-1 / 18)), (6, (1 / 144))]

def value1217 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 72))]

def value1218 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (9, (-1 / 36))]

def value1219 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (5, (-1 / 18)), (27, (1 / 6)), (68, (1 / 12))]

def value1220 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (5, (-1 / 36))]

def value1221 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (13 / 144)), (2, (-1 / 18))]

def value1222 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (1 / 48)), (5, (-1 / 18)), (27, (1 / 12))]

def value1223 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (25, (-1 / 3)), (26, (1 / 9)), (54, (-1 / 3))]

def value1224 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 48)), (5, (-1 / 18)), (6, (1 / 72)), (68, (1 / 12))]

def value1225 : Sparse (Fin 909) := [(1, (-1 / 18)), (2, (13 / 144)), (6, (1 / 144))]

def value1226 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (226, (-1 / 3))]

def value1227 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 9)), (6, (-1 / 36)), (9, (-1 / 36))]

def value1228 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-5 / 144)), (5, (1 / 36)), (6, (-7 / 144))]

def value1229 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (35, (1 / 9)), (82, (1 / 9)), (199, (-1 / 3)), (723, (-1 / 3))]

def value1230 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 48)), (5, (-1 / 36)), (6, (1 / 72)), (52, (1 / 9)), (228, (-1 / 3)), (728, (-1 / 3))]

def value1231 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-7 / 144)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value1232 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 48)), (7, (1 / 9)), (11, (1 / 9)), (35, (2 / 9))]

def value1233 : Sparse (Fin 909) := [(7, (2 / 9)), (69, (2 / 9)), (70, (2 / 9)), (256, (-1 / 3))]

def value1234 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (2 / 9)), (35, (2 / 9)), (81, (-1 / 3))]

def value1235 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (2 / 9)), (13, (2 / 9)), (33, (-1 / 3))]

def value1236 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 12)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9)), (308, (-1 / 3))]

def value1237 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 48)), (2, (1 / 72)), (27, (1 / 12)), (30, (-1 / 3))]

def value1238 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (201, (-1 / 3)), (726, (-1 / 3))]

def value1239 : Sparse (Fin 909) := [(3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9)), (56, (-1 / 3)), (228, (-1 / 3))]

def value1240 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (2 / 9)), (69, (1 / 9)), (71, (5 / 9))]

def value1241 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 144)), (2, (1 / 144))]

def value1242 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 48))]

def value1243 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 9)), (6, (1 / 144)), (7, (2 / 9)), (8, (2 / 9))]

def value1244 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 48)), (2, (1 / 72)), (27, (1 / 12)), (31, (-1 / 3))]

def value1245 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-5 / 72)), (2, (1 / 144)), (4, (1 / 9))]

def value1246 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (5 / 144)), (4, (1 / 9))]

def value1247 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 18)), (2, (1 / 36)), (31, (-1 / 3))]

def value1248 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (51, (-2 / 3)), (52, (1 / 9))]

def value1249 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 3)), (4, (2 / 9)), (26, (1 / 3))]

def value1250 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (55, (-2 / 3))]

def value1251 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-2 / 3))]

def value1252 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (-1 / 144)), (5, (1 / 36))]

def value1253 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 36)), (2, (5 / 144)), (5, (-1 / 36)), (27, (1 / 6))]

def value1254 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (277, (-1 / 3))]

def value1255 : Sparse (Fin 909) := [(3, (1 / 9)), (10, (-1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (55, (-1 / 3))]

def value1256 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (51, (-1 / 3)), (127, (-1 / 3))]

def value1257 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 3)), (35, (1 / 9))]

def value1258 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (2 / 9)), (70, (1 / 9)), (71, (1 / 9)), (277, (-1 / 3))]

def value1259 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-1 / 12)), (2, (-1 / 144))]

def value1260 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-7 / 144)), (2, (1 / 48))]

def value1261 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 144)), (2, (1 / 24)), (5, (-1 / 36))]

def value1262 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 24)), (2, (1 / 144))]

def value1263 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-11 / 144)), (2, (1 / 36)), (27, (1 / 12))]

def value1264 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (13 / 144)), (2, (1 / 144))]

def value1265 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 48))]

def value1266 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (1 / 9)), (124, (-1 / 3)), (126, (-1 / 3))]

def value1267 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 18)), (5, (-1 / 36))]

def value1268 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (2, (-1 / 18))]

def value1269 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (54, (-1 / 3))]

def value1270 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value1271 : Sparse (Fin 909) := [(7, (1 / 9)), (35, (1 / 9)), (70, (1 / 9)), (125, (-1 / 3)), (197, (-1 / 3))]

def value1272 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 72)), (5, (-1 / 18)), (6, (5 / 144))]

def value1273 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (2 / 9)), (492, (-1 / 3))]

def value1274 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (52, (1 / 9)), (237, (-1 / 3)), (308, (-1 / 3))]

def value1275 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (727, (-1 / 3))]

def value1276 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (31, (-1 / 3)), (51, (-1 / 3))]

def value1277 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3))]

def value1278 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (35, (1 / 9)), (52, (2 / 9)), (228, (-1 / 3))]

def value1279 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (71, (1 / 9)), (126, (-1 / 3)), (236, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1280 : Sparse (Fin 909) := [(0, (-53 / 720)), (1, (1 / 144))]

def value1281 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (-1 / 9)), (4, (1 / 9)), (12, (1 / 9))]

def value1282 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (1 / 9)), (52, (-1 / 9))]

def value1283 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (-1 / 9))]

def value1284 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 72)), (2, (-1 / 144))]

def value1285 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (-1 / 9))]

def value1286 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144)), (3, (-1 / 9)), (52, (1 / 9))]

def value1287 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (11 / 96)), (6, (1 / 96)), (13, (1 / 6)), (35, (1 / 6))]

def value1288 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value1290 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 12)), (5, (1 / 6)), (6, (-1 / 24))]

def value1291 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 48))]

def value1292 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 12)), (2, (-1 / 24))]

def value1293 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 8)), (2, (-1 / 12))]

def value1294 : Sparse (Fin 909) := [(0, (-7 / 120)), (1, (-1 / 24))]

def value1295 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9))]

def value1296 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9))]

def value1297 : Sparse (Fin 909) := [(7, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9)), (70, (1 / 9))]

def value1298 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9))]

def value1299 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (8, (1 / 9))]

def value1300 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (-1 / 9)), (70, (1 / 9))]

def value1301 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (-1 / 9)), (7, (1 / 9))]

def value1302 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (-1 / 9)), (8, (1 / 9)), (69, (1 / 9))]

def value1303 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 72)), (5, (-1 / 36)), (123, (-1 / 3)), (124, (-1 / 3))]

def value1304 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 72)), (2, (1 / 144)), (23, (-1 / 3)), (25, (-1 / 3))]

def value1305 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (64, (-1 / 3)), (125, (-1 / 3))]

def value1306 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 3)), (52, (2 / 9))]

def value1307 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (52, (-1 / 9)), (69, (1 / 9))]

def value1308 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9)), (126, (-1 / 3))]

def value1309 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9)), (24, (-1 / 3))]

def value1310 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (51, (-1 / 3)), (126, (-1 / 3))]

def value1311 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 144)), (2, (1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9))]

def value1312 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 18)), (2, (7 / 144)), (5, (-1 / 18)), (13, (1 / 9)), (52, (2 / 9)), (69, (1 / 9))]

def value1313 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (125, (-1 / 3))]

def value1314 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (12, (2 / 9)), (23, (-1 / 3))]

def value1315 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (51, (-1 / 3)), (124, (-1 / 3))]

def value1316 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (4, (1 / 9)), (7, (1 / 9))]

def value1317 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (7, (1 / 9)), (52, (1 / 9)), (69, (1 / 9))]

def value1318 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (197, (-1 / 3))]

def value1319 : Sparse (Fin 909) := [(24, (-1 / 3)), (55, (-1 / 3)), (197, (-1 / 3))]

def value1320 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 144)), (3, (1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (13, (1 / 9)), (35, (2 / 9)), (70, (1 / 9))]

def value1321 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (196, (-1 / 3))]

def value1322 : Sparse (Fin 909) := [(23, (-1 / 3)), (55, (-1 / 3)), (125, (-1 / 3))]

def value1323 : Sparse (Fin 909) := [(0, (-13 / 60)), (1, (-3 / 4)), (2, (1 / 6))]

def value1324 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (7 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (52, (1 / 9)), (818, (-1 / 3))]

def value1325 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (1 / 18)), (6, (1 / 144)), (228, (-1 / 3)), (726, (-1 / 3))]

def value1326 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (52, (1 / 9))]

def value1327 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 48)), (52, (1 / 9)), (237, (-1 / 3))]

def value1328 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (-1 / 72)), (5, (1 / 36)), (6, (1 / 144)), (9, (-1 / 36))]

def value1329 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (55, (-1 / 3)), (228, (-1 / 3))]

def value1330 : Sparse (Fin 909) := [(253, (1 / 1))]

def value1331 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 12)), (31, (-1 / 3)), (237, (-1 / 3))]

def value1332 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (238, (-1 / 3))]

def value1333 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (5 / 144)), (3, (1 / 9)), (31, (-1 / 3))]

def value1334 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (-1 / 36)), (3, (1 / 9))]

def value1335 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (1 / 48)), (5, (-1 / 36))]

def value1336 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-5 / 144)), (2, (1 / 36)), (3, (2 / 9)), (4, (1 / 9)), (52, (1 / 9))]

def value1337 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (5, (-1 / 36)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value1338 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (1 / 18)), (6, (1 / 144)), (201, (-1 / 3)), (796, (-1 / 3))]

def value1339 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 24)), (6, (1 / 144)), (237, (-1 / 3))]

def value1340 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (52, (1 / 9))]

def value1341 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 16)), (2, (1 / 16)), (5, (-1 / 9)), (6, (1 / 144)), (8, (1 / 9)), (52, (1 / 9))]

def value1342 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9)), (309, (-1 / 3))]

def value1343 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 18)), (6, (-1 / 144)), (11, (1 / 9)), (35, (1 / 9)), (728, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value329 : Sparse (Fin 909) := [(263, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1344 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 9)), (2, (-1 / 72)), (27, (1 / 12))]

def value1345 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 144)), (5, (-1 / 36))]

def value1346 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-7 / 144)), (2, (1 / 72)), (3, (1 / 9)), (12, (1 / 9)), (51, (-1 / 3))]

def value1347 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 18)), (2, (-1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3))]

def value1348 : Sparse (Fin 909) := [(1, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3))]

def value1349 : Sparse (Fin 909) := [(0, (-3 / 80)), (1, (-1 / 36)), (2, (1 / 144))]

def value1350 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 12)), (2, (-5 / 72))]

def value1351 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 9)), (51, (-1 / 3))]

def value1352 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 144)), (3, (1 / 9)), (13, (1 / 9)), (56, (-1 / 3))]

def value1353 : Sparse (Fin 909) := [(1, (1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (35, (1 / 9)), (82, (1 / 9)), (796, (-1 / 3))]

def value1354 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (5, (-1 / 18)), (71, (1 / 9))]

def value1355 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9))]

def value1356 : Sparse (Fin 909) := [(2, (1 / 48)), (6, (-1 / 144)), (11, (1 / 9)), (35, (2 / 9)), (70, (1 / 9))]

def value1357 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 36)), (2, (1 / 72))]

def value1358 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (2 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (262, (-1 / 3))]

def value1359 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (236, (-1 / 3))]

def value1360 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-1 / 72)), (2, (1 / 72)), (30, (-1 / 3))]

def value1361 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 36)), (2, (5 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (236, (-1 / 3))]

def value1362 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 72)), (2, (1 / 36)), (8, (1 / 9))]

def value1363 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 36)), (5, (-1 / 18)), (6, (1 / 72)), (71, (1 / 9))]

def value1364 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (256, (-1 / 3))]

def value1365 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 18)), (6, (1 / 144)), (26, (1 / 9)), (35, (1 / 9)), (197, (-1 / 3))]

def value1366 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (126, (-1 / 3))]

def value1367 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 144)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9)), (71, (1 / 9))]

def value1368 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 12)), (30, (-1 / 3)), (236, (-1 / 3))]

def value1369 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (56, (-1 / 3)), (197, (-1 / 3))]

def value1370 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (24, (-1 / 3)), (27, (1 / 12)), (126, (-1 / 3))]

def value1371 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 18)), (8, (2 / 9)), (71, (1 / 9))]

def value1372 : Sparse (Fin 909) := [(51, (-1 / 3)), (56, (-1 / 3)), (262, (-1 / 3))]

def value1373 : Sparse (Fin 909) := [(2, (-1 / 24)), (6, (-1 / 24)), (723, (-2 / 3))]

def value1374 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 24)), (54, (-2 / 3))]

def value1375 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 72)), (6, (1 / 144)), (196, (-1 / 3)), (226, (-1 / 3))]

def value1376 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 36)), (54, (-1 / 3)), (125, (-1 / 3))]

def value1377 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (23, (-1 / 3)), (27, (1 / 12)), (124, (-1 / 3))]

def value1378 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (7, (2 / 9)), (69, (1 / 9))]

def value1379 : Sparse (Fin 909) := [(2, (-1 / 96)), (5, (1 / 2)), (6, (-3 / 32)), (7, (-1 / 1)), (9, (5 / 24)), (35, (-1 / 2)), (69, (-3 / 2)), (70, (-4 / 3)), (71, (-1 / 1)), (257, (-1 / 3))]

def value1380 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (2, (-7 / 96)), (3, (-1 / 2)), (5, (7 / 24)), (6, (-1 / 32)), (7, (-1 / 2)), (9, (1 / 24)), (35, (-5 / 6)), (52, (-1 / 1)), (69, (-1 / 1)), (70, (-1 / 2)), (71, (-1 / 2)), (256, (3 / 2)), (257, (-1 / 3)), (495, (-1 / 2))]

def value1381 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-19 / 96)), (2, (-7 / 32)), (5, (7 / 12)), (6, (-5 / 96)), (7, (-1 / 6)), (8, (-1 / 1)), (9, (1 / 6)), (52, (-1 / 3)), (69, (-7 / 6)), (70, (-1 / 6)), (71, (-5 / 2)), (256, (1 / 2)), (495, (-1 / 6))]

def value1382 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-5 / 48)), (3, (-1 / 3)), (5, (3 / 8)), (6, (-1 / 32)), (7, (-1 / 1)), (8, (-1 / 3)), (9, (1 / 8)), (35, (-2 / 3)), (52, (-1 / 3)), (69, (-4 / 3)), (70, (-5 / 6)), (71, (-1 / 1)), (256, (1 / 1)), (257, (-1 / 3)), (495, (-1 / 3))]

def value1383 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (5 / 96)), (5, (5 / 24)), (6, (-1 / 48)), (7, (-1 / 6)), (9, (1 / 6)), (26, (-1 / 6)), (35, (-1 / 2)), (69, (-1 / 6)), (70, (-1 / 6)), (71, (-1 / 3)), (259, (1 / 2)), (495, (-1 / 6))]

def value1384 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 6)), (2, (-17 / 96)), (3, (-1 / 6)), (5, (11 / 24)), (6, (-7 / 96)), (8, (-1 / 6)), (9, (1 / 8)), (13, (-1 / 3)), (35, (-1 / 6)), (52, (-2 / 3)), (69, (-1 / 3)), (71, (-1 / 3)), (128, (-1 / 3)), (262, (1 / 2)), (495, (-1 / 3))]

def value1385 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 96)), (2, (-3 / 32)), (3, (-1 / 3)), (5, (1 / 3)), (6, (-7 / 96)), (7, (-1 / 6)), (9, (1 / 12)), (13, (-2 / 3)), (35, (-4 / 3)), (52, (-4 / 3)), (60, (-5 / 6)), (69, (-1 / 6)), (70, (-1 / 6)), (128, (-2 / 3)), (257, (-1 / 3)), (260, (1 / 2)), (495, (-1 / 2))]

def value1386 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (7 / 48)), (3, (-1 / 6)), (5, (7 / 24)), (6, (-1 / 16)), (7, (-1 / 2)), (26, (-1 / 2)), (35, (-1 / 1)), (54, (3 / 2)), (259, (3 / 2)), (260, (1 / 1)), (495, (-1 / 6))]

def value1387 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 96)), (2, (1 / 96)), (3, (-1 / 1)), (5, (7 / 24)), (6, (-1 / 24)), (7, (-1 / 2)), (13, (-1 / 2)), (35, (-4 / 3)), (52, (-1 / 1)), (60, (-1 / 3))]

def value1388 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-7 / 96)), (2, (-3 / 32)), (3, (-1 / 1)), (5, (1 / 8)), (6, (-1 / 96)), (12, (-1 / 2)), (13, (-11 / 6)), (35, (-1 / 2)), (52, (-1 / 1)), (59, (3 / 2)), (60, (-1 / 3)), (128, (-1 / 2))]

def value1389 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 8)), (2, (-1 / 8)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (7 / 24)), (6, (-1 / 32)), (8, (-1 / 3)), (13, (-1 / 3)), (26, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 2)), (56, (1 / 1)), (59, (1 / 2)), (128, (-1 / 6)), (259, (1 / 2)), (262, (2 / 1)), (495, (-1 / 6))]

def value1390 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-1 / 4)), (2, (-25 / 96)), (3, (-1 / 6)), (5, (2 / 3)), (6, (-1 / 12)), (7, (-1 / 3)), (8, (-2 / 3)), (13, (-1 / 3)), (35, (-1 / 6)), (52, (-2 / 3)), (59, (1 / 2)), (128, (-1 / 6))]

def value1391 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 8)), (2, (-5 / 24)), (3, (-1 / 1)), (5, (5 / 12)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-1 / 3)), (12, (-1 / 6)), (13, (-2 / 3)), (35, (-7 / 6)), (52, (-1 / 1)), (59, (1 / 2)), (60, (-1 / 3)), (128, (-1 / 6))]

def value1392 : Sparse (Fin 909) := [(1, (3 / 32)), (2, (3 / 32)), (3, (-1 / 2)), (5, (1 / 12)), (6, (-1 / 24)), (7, (-2 / 3)), (13, (-1 / 6)), (26, (-2 / 3)), (34, (-1 / 6)), (35, (-4 / 3)), (67, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 2)), (124, (1 / 2)), (196, (1 / 2)), (197, (1 / 1)), (257, (-1 / 6)), (266, (1 / 2))]

def value1393 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (-1 / 48)), (3, (-1 / 3)), (5, (1 / 12)), (13, (-1 / 3)), (33, (1 / 2)), (52, (-1 / 3)), (55, (1 / 1)), (64, (1 / 1)), (125, (1 / 1)), (197, (1 / 2)), (260, (1 / 2)), (263, (-1 / 1))]

def value1394 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 1)), (35, (-1 / 6)), (54, (1 / 1)), (55, (1 / 2)), (63, (1 / 2)), (65, (1 / 2)), (124, (1 / 2)), (125, (3 / 2)), (196, (1 / 1)), (197, (1 / 2)), (264, (1 / 1)), (266, (1 / 2))]

def value1395 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-1 / 24)), (3, (-5 / 6)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-2 / 3)), (13, (-1 / 2)), (26, (-1 / 3)), (34, (-1 / 6)), (35, (-1 / 1)), (52, (-1 / 3)), (60, (-1 / 6)), (64, (1 / 2)), (67, (-1 / 6)), (69, (-1 / 6)), (70, (-1 / 3)), (125, (1 / 1)), (126, (1 / 2)), (197, (1 / 2)), (257, (-1 / 6)), (260, (1 / 2)), (268, (1 / 2))]

def value1396 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-1 / 96)), (23, (1 / 2)), (24, (1 / 2)), (27, (-1 / 8)), (51, (1 / 2)), (54, (1 / 2)), (55, (1 / 2)), (56, (1 / 2)), (61, (1 / 2)), (124, (1 / 2)), (125, (1 / 2)), (126, (1 / 2)), (196, (1 / 2)), (197, (1 / 1)), (263, (-1 / 1)), (266, (1 / 2)), (268, (1 / 2))]

def value1397 : Sparse (Fin 909) := [(3, (-1 / 3)), (5, (1 / 12)), (7, (-1 / 3)), (13, (-2 / 3)), (32, (-1 / 6)), (35, (-2 / 3)), (52, (-1 / 3)), (54, (1 / 1)), (60, (-1 / 3)), (62, (1 / 1)), (69, (-1 / 6)), (70, (-1 / 6)), (125, (1 / 1)), (257, (-1 / 6)), (260, (1 / 1)), (264, (3 / 2))]

def value1398 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-7 / 96)), (6, (-1 / 48)), (13, (-1 / 3)), (32, (-1 / 6)), (35, (-1 / 6)), (60, (-1 / 3)), (63, (1 / 2)), (70, (-1 / 6)), (196, (1 / 2)), (257, (-1 / 6)), (264, (1 / 2))]

def value1399 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 96)), (5, (1 / 12)), (6, (-1 / 32)), (7, (-1 / 3)), (9, (1 / 8)), (26, (-1 / 3)), (35, (-1 / 2)), (67, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 3)), (257, (-1 / 3)), (495, (-1 / 3))]

def value1400 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (-1 / 96)), (3, (-1 / 3)), (5, (1 / 12)), (13, (-1 / 6)), (34, (-1 / 6)), (52, (-1 / 6)), (60, (-1 / 6)), (64, (1 / 2)), (69, (-1 / 6)), (125, (1 / 2)), (128, (-1 / 3)), (260, (1 / 2)), (495, (-1 / 6))]

def value1401 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-1 / 24)), (3, (-5 / 6)), (5, (1 / 12)), (12, (-1 / 3)), (13, (-7 / 6)), (35, (-1 / 3)), (52, (-2 / 3)), (59, (1 / 1)), (61, (1 / 2)), (256, (1 / 2)), (263, (-1 / 1))]

def value1402 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-1 / 32)), (3, (-2 / 3)), (12, (-1 / 3)), (13, (-13 / 6)), (32, (-1 / 2)), (35, (-5 / 6)), (52, (-2 / 3)), (54, (1 / 2)), (60, (-5 / 6)), (62, (1 / 1)), (128, (-1 / 3)), (257, (-1 / 6)), (260, (1 / 2)), (264, (1 / 2)), (495, (-1 / 6))]

def value1403 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (1 / 96)), (3, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 32)), (26, (-1 / 6)), (34, (-1 / 6)), (35, (-1 / 6)), (54, (1 / 2)), (67, (-1 / 3)), (257, (-1 / 6)), (259, (1 / 2)), (266, (1 / 2)), (495, (-1 / 6))]

def value1404 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (2, (-1 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 96)), (13, (-1 / 2)), (26, (-1 / 2)), (34, (-1 / 3)), (35, (-2 / 3)), (52, (-1 / 2)), (56, (1 / 2)), (60, (-1 / 3)), (67, (-1 / 6)), (128, (-1 / 6)), (257, (-1 / 6)), (262, (1 / 2)), (268, (1 / 2)), (495, (-1 / 6))]

def value1405 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 24)), (2, (-5 / 96)), (3, (-5 / 6)), (5, (1 / 6)), (6, (-1 / 24)), (13, (-2 / 3)), (26, (-1 / 3)), (34, (-1 / 3)), (35, (-2 / 3)), (52, (-2 / 3)), (60, (-1 / 3)), (128, (-1 / 6))]

def value1406 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 32)), (2, (1 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (12, (-1 / 3)), (13, (-2 / 3)), (26, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 1)), (54, (1 / 1)), (55, (1 / 2)), (56, (1 / 1)), (59, (1 / 2)), (61, (1 / 1)), (259, (1 / 2)), (262, (1 / 2)), (266, (1 / 2)), (268, (1 / 2))]

def value1407 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 48)), (2, (-1 / 16)), (3, (-2 / 3)), (5, (1 / 12)), (6, (-1 / 48)), (12, (-1 / 6)), (13, (-8 / 3)), (32, (-2 / 3)), (35, (-2 / 3)), (52, (-2 / 3)), (60, (-2 / 3)), (62, (1 / 1)), (128, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2368 : Sparse (Fin 909) := [(1, (1 / 288)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (35, (-1 / 18)), (87, (-1 / 2)), (228, (1 / 6)), (498, (-1 / 2)), (764, (-1 / 2))]

def value2369 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 96)), (2, (1 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (54, (1 / 6)), (89, (-1 / 2)), (123, (1 / 6)), (226, (1 / 6))]

def value2370 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-1 / 48)), (6, (-1 / 288)), (23, (1 / 6)), (25, (1 / 6)), (63, (1 / 6)), (123, (1 / 6)), (196, (1 / 6)), (216, (-1 / 2)), (226, (1 / 6))]

def value2371 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-1 / 32)), (5, (1 / 72)), (6, (-1 / 288)), (23, (1 / 6)), (25, (1 / 6)), (87, (-1 / 2)), (123, (1 / 6)), (124, (1 / 6)), (196, (1 / 6)), (226, (1 / 6))]

def value2372 : Sparse (Fin 909) := [(0, (-1 / 1440)), (2, (-1 / 288)), (23, (1 / 6)), (25, (1 / 3)), (31, (1 / 6)), (87, (-1 / 2)), (108, (-1 / 2))]

def value2373 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (25, (1 / 3)), (31, (1 / 3)), (87, (-1 / 2)), (123, (1 / 3)), (226, (1 / 6)), (237, (1 / 6))]

def value2374 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (31, (1 / 3)), (123, (1 / 3)), (226, (1 / 6))]

def value2375 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-17 / 96)), (2, (-9 / 32)), (5, (3 / 4)), (6, (-7 / 48)), (8, (-1 / 3)), (9, (5 / 8)), (52, (-1 / 3)), (58, (-1 / 48)), (69, (-1 / 6)), (71, (-2 / 3)), (310, (-1 / 3)), (495, (-1 / 3)), (818, (1 / 1))]

def value2376 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 8)), (5, (1 / 2)), (6, (-1 / 8)), (9, (5 / 6)), (58, (-1 / 24))]

def value2377 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-13 / 96)), (2, (-17 / 96)), (5, (1 / 2)), (6, (-1 / 16)), (8, (-2 / 3)), (9, (1 / 24)), (52, (-1 / 3)), (69, (-1 / 6)), (71, (-2 / 3))]

def value2378 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-1 / 96)), (3, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 48)), (7, (-1 / 3)), (9, (1 / 24)), (35, (-1 / 3)), (52, (-1 / 3)), (69, (-1 / 3)), (70, (-1 / 6)), (71, (-1 / 3))]

def value2379 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-7 / 48)), (2, (-3 / 16)), (3, (-1 / 3)), (5, (3 / 8)), (6, (-1 / 24)), (7, (-1 / 6)), (8, (-1 / 3)), (35, (-1 / 3)), (52, (-2 / 3))]

def value2380 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-3 / 16)), (3, (-1 / 3)), (5, (13 / 24)), (6, (-1 / 12)), (7, (-1 / 6)), (8, (-1 / 3)), (35, (-1 / 3)), (52, (-2 / 3))]

def value2381 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 96)), (2, (5 / 96)), (3, (-1 / 6)), (5, (1 / 12)), (7, (-1 / 3)), (8, (-1 / 6)), (11, (-1 / 6)), (26, (-1 / 6)), (35, (-1 / 2)), (52, (-1 / 6)), (228, (1 / 2))]

def value2382 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-5 / 48)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 3)), (6, (-1 / 16)), (11, (-1 / 6)), (26, (-1 / 3)), (35, (-2 / 3)), (52, (-5 / 6)), (228, (1 / 2))]

def value2383 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (1 / 24)), (3, (-1 / 6)), (5, (1 / 3)), (6, (1 / 48)), (9, (1 / 12)), (11, (-1 / 3)), (26, (-1 / 3)), (35, (-2 / 3)), (52, (-1 / 3)), (58, (-1 / 96)), (278, (-1 / 6)), (495, (-1 / 3))]

def value2384 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 4)), (2, (1 / 6))]

def value2385 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-5 / 96)), (5, (1 / 8)), (6, (-1 / 96)), (7, (-1 / 9)), (8, (-2 / 9)), (9, (1 / 36)), (69, (-1 / 6)), (70, (-1 / 18)), (71, (-1 / 3))]

def value2386 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 288)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 9)), (9, (1 / 36)), (69, (-5 / 18)), (70, (-1 / 6)), (71, (-1 / 9))]

def value2387 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 48)), (5, (1 / 18)), (6, (-1 / 144)), (8, (-1 / 9)), (9, (1 / 36)), (69, (-1 / 9)), (71, (-4 / 9))]

def value2388 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (-1 / 36)), (6, (1 / 96)), (7, (-1 / 9)), (9, (1 / 36)), (35, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2389 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 18)), (2, (1 / 96)), (3, (-1 / 3)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-5 / 18)), (35, (-5 / 18)), (60, (-1 / 9))]

def value2390 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 96)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (7 / 72)), (6, (-1 / 72)), (7, (-1 / 9)), (8, (-1 / 9)), (35, (-1 / 18))]

def value2391 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 288)), (2, (-1 / 18)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9))]

def value2392 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-13 / 288)), (2, (-5 / 72)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (5 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (13, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 6)), (59, (1 / 6)), (128, (-1 / 18))]

def value2393 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 48)), (3, (-1 / 3)), (5, (1 / 72)), (7, (-1 / 18)), (10, (1 / 6)), (12, (-2 / 9)), (13, (-1 / 3)), (35, (-1 / 9)), (52, (-1 / 9)), (59, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 18))]

def value2394 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 9))]

def value2395 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (13 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 96)), (35, (-1 / 18))]

def value2396 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 96)), (2, (-7 / 288)), (3, (-2 / 9)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 9)), (13, (-2 / 9)), (35, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 9)), (59, (1 / 6)), (60, (-1 / 18)), (128, (-1 / 18))]

def value2397 : Sparse (Fin 909) := [(3, (-1 / 18)), (7, (-1 / 18)), (10, (1 / 6)), (13, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 18)), (59, (1 / 6)), (60, (-1 / 18)), (82, (-1 / 18)), (128, (-1 / 18))]

def value2398 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-1 / 72)), (5, (1 / 72)), (12, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (60, (-1 / 18))]

def value2399 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 288)), (2, (-1 / 16)), (3, (-1 / 9)), (5, (7 / 72)), (6, (-1 / 96)), (7, (-1 / 9)), (8, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2400 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 144)), (2, (-1 / 24)), (5, (1 / 9)), (6, (-1 / 96)), (7, (-1 / 18)), (8, (-1 / 6)), (52, (-1 / 18))]

def value2401 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (-1 / 36)), (5, (1 / 24)), (6, (-1 / 144)), (52, (-1 / 18))]

def value2402 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 9))]

def value2403 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-5 / 144)), (3, (-2 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2404 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 48)), (3, (-1 / 6)), (5, (1 / 36)), (6, (-1 / 144)), (7, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (35, (-1 / 9)), (69, (-1 / 18)), (70, (-1 / 18)), (124, (1 / 6)), (196, (1 / 6))]

def value2405 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-5 / 288)), (3, (-2 / 9)), (5, (1 / 36)), (7, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 9)), (23, (1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (69, (-1 / 18)), (70, (-1 / 18)), (125, (1 / 3))]

def value2406 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18)), (125, (1 / 6)), (126, (1 / 6))]

def value2407 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18))]

def value2408 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2409 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 18)), (2, (-1 / 288)), (3, (-1 / 18)), (6, (-1 / 144)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18))]

def value2410 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 16)), (2, (-5 / 288)), (3, (-2 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (54, (1 / 6))]

def value2411 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 16)), (2, (-11 / 288)), (3, (-1 / 3)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 6)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2412 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (7, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 9)), (52, (-1 / 18))]

def value2413 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (2, (1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (12, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6))]

def value2414 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (12, (-1 / 18)), (13, (-5 / 18)), (35, (-1 / 9)), (52, (-2 / 9)), (60, (-1 / 9)), (82, (-1 / 18)), (128, (-1 / 6))]

def value2415 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 36)), (6, (-1 / 144)), (12, (-1 / 9)), (13, (-2 / 9)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2416 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (5, (1 / 24)), (6, (-1 / 144)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9))]

def value2417 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 9)), (60, (-1 / 9)), (128, (-1 / 18))]

def value2418 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 32)), (2, (-1 / 288)), (3, (-1 / 6)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2419 : Sparse (Fin 909) := [(0, (-11 / 720)), (1, (29 / 288)), (2, (-5 / 288)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18))]

def value2420 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (19 / 288)), (2, (-5 / 144)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 6))]

def value2421 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 72)), (3, (-5 / 18)), (12, (-1 / 9)), (13, (-5 / 18))]

def value2422 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 96)), (2, (1 / 96)), (12, (-1 / 18)), (13, (-1 / 18))]

def value2423 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (1 / 32)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 9)), (12, (-1 / 18)), (23, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6))]

def value2424 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (7 / 72)), (2, (-1 / 288)), (3, (-1 / 6)), (12, (-1 / 9)), (13, (-1 / 9))]

def value2425 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 72)), (2, (5 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (13, (-1 / 18))]

def value2426 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 72)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (54, (1 / 6))]

def value2427 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 48)), (3, (-2 / 9)), (13, (-2 / 9))]

def value2428 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (13 / 288)), (2, (-1 / 288)), (3, (-1 / 9)), (12, (-1 / 6)), (13, (-1 / 6))]

def value2429 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 96)), (2, (-5 / 144)), (3, (-1 / 3)), (5, (1 / 72)), (7, (-1 / 9)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6))]

def value2430 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-7 / 18)), (32, (-1 / 9))]

def value2431 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2432 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 18)), (24, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (55, (1 / 6))]

def value2433 : Sparse (Fin 909) := [(1, (5 / 288)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 9)), (26, (-2 / 9)), (35, (-5 / 18)), (52, (-1 / 9)), (67, (-1 / 9))]

def value2434 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (25 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18))]

def value2435 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 36)), (2, (-1 / 96)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (55, (1 / 6))]

def value2436 : Sparse (Fin 909) := [(1, (-13 / 288)), (2, (7 / 144)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18))]

def value2437 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (5 / 288)), (3, (-1 / 6)), (6, (-1 / 288)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-5 / 18)), (67, (-1 / 9))]

def value2438 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (19 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18))]

def value2439 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 72)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 18))]

def value2440 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (13 / 288)), (2, (1 / 48)), (3, (-1 / 9)), (12, (-1 / 18)), (26, (-1 / 18))]

def value2441 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 18)), (2, (-1 / 96)), (3, (-7 / 18)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-2 / 9)), (26, (-1 / 9)), (34, (-1 / 9))]

def value2442 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (35 / 288)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 9)), (26, (-1 / 18))]

def value2443 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 288)), (2, (-5 / 288)), (3, (-1 / 6)), (26, (-1 / 18))]

def value2444 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 288)), (2, (1 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (13, (-1 / 18)), (26, (-2 / 9)), (34, (-1 / 9))]

def value2445 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 36)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-1 / 6)), (26, (-1 / 18))]

def value2446 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 96)), (2, (1 / 288)), (3, (-2 / 9)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 9)), (34, (-1 / 9))]

def value2447 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 18)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (26, (-1 / 9))]

def value2448 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (11 / 144)), (2, (-7 / 288)), (3, (-1 / 18)), (12, (-1 / 18))]

def value2449 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (4, (-1 / 18))]

def value2450 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (5 / 72)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-2 / 9)), (12, (-1 / 18)), (26, (-1 / 9))]

def value2451 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 144)), (3, (-2 / 9)), (12, (-1 / 6)), (13, (-1 / 9)), (26, (-1 / 18)), (33, (1 / 6)), (34, (-1 / 18))]

def value2452 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 36)), (2, (-1 / 288)), (3, (-2 / 9)), (4, (-1 / 6)), (13, (-1 / 18)), (26, (-1 / 9)), (33, (1 / 6)), (34, (-1 / 18))]

def value2453 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (7 / 144)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 9))]

def value2454 : Sparse (Fin 909) := [(0, (-29 / 1440)), (1, (37 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 18))]

def value2455 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-13 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (13, (-1 / 18))]

def value2456 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 8)), (2, (-17 / 96)), (5, (1 / 2)), (6, (-7 / 96)), (8, (-2 / 3)), (9, (1 / 12)), (27, (-1 / 8)), (68, (-1 / 4)), (71, (-1 / 2)), (126, (1 / 2)), (236, (1 / 1))]

def value2457 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (1 / 96)), (5, (1 / 4)), (6, (-5 / 96)), (8, (-1 / 6)), (9, (1 / 12)), (26, (-1 / 6)), (35, (-1 / 6)), (56, (1 / 2)), (68, (-1 / 4)), (71, (-1 / 3)), (197, (1 / 1)), (236, (1 / 2)), (796, (1 / 2))]

def value2458 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (-1 / 48)), (5, (1 / 4)), (6, (-1 / 24)), (8, (-1 / 3)), (9, (1 / 24)), (71, (-1 / 3)), (236, (1 / 2))]

def value2459 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-1 / 48)), (2, (-1 / 6)), (5, (1 / 4)), (6, (-1 / 48)), (8, (-1 / 2)), (30, (1 / 2)), (71, (-1 / 3)), (236, (1 / 1))]

def value2460 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-5 / 96)), (2, (-5 / 48)), (3, (-1 / 3)), (5, (5 / 24)), (6, (-1 / 96)), (7, (-1 / 3)), (8, (-1 / 3)), (27, (-1 / 8)), (52, (-1 / 6)), (69, (-1 / 6)), (71, (-1 / 6)), (126, (1 / 2)), (236, (1 / 2))]

def value2461 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-1 / 24)), (3, (-1 / 6)), (5, (5 / 24)), (6, (-1 / 32)), (7, (-1 / 6)), (9, (1 / 24)), (26, (-1 / 3)), (35, (-1 / 2)), (70, (-1 / 6)), (71, (-1 / 6)), (197, (1 / 2))]

def value2462 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 4)), (2, (-5 / 48)), (3, (-1 / 3)), (5, (5 / 24)), (6, (-1 / 48)), (7, (-1 / 6)), (8, (-1 / 3))]

def value2463 : Sparse (Fin 909) := [(1, (-1 / 16)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 48)), (7, (-1 / 3)), (8, (-1 / 6)), (26, (-1 / 3)), (35, (-1 / 6))]

def value2464 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (7 / 48)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (5 / 24)), (13, (-1 / 3)), (26, (-1 / 3)), (35, (-2 / 3)), (82, (-1 / 6))]

def value2465 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 48)), (2, (-1 / 24)), (3, (-1 / 3)), (5, (1 / 4)), (6, (-1 / 48)), (52, (-1 / 3)), (237, (1 / 2))]

def value2466 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 12)), (2, (-7 / 48)), (3, (-1 / 3)), (5, (5 / 24)), (6, (-1 / 48)), (8, (-1 / 3)), (52, (-1 / 6))]

def value2467 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 8)), (3, (-2 / 3)), (5, (1 / 6)), (6, (-1 / 32)), (7, (-1 / 3)), (26, (-1 / 3)), (35, (-1 / 6))]

def value2468 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 96)), (2, (-5 / 96)), (3, (-1 / 6)), (5, (5 / 24)), (11, (-1 / 6)), (13, (-1 / 3)), (26, (-1 / 3)), (35, (-2 / 3)), (52, (-1 / 6))]

def value2469 : Sparse (Fin 909) := [(0, (-11 / 480)), (1, (5 / 16)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-1 / 3)), (26, (-1 / 3))]

def value2470 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 96)), (2, (-11 / 96)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 32)), (26, (-1 / 6)), (31, (1 / 2)), (35, (-1 / 6)), (52, (-1 / 3)), (237, (1 / 2)), (238, (1 / 2))]

def value2471 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (5 / 96)), (2, (-5 / 48)), (3, (-2 / 3)), (4, (-1 / 3)), (5, (1 / 12)), (6, (-1 / 96)), (26, (-1 / 3)), (35, (-1 / 6)), (52, (-1 / 3))]

def value2472 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (5 / 96)), (2, (-1 / 24)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 48)), (26, (-1 / 3)), (27, (-1 / 4)), (52, (-1 / 6)), (55, (1 / 1)), (228, (1 / 2)), (237, (1 / 2))]

def value2473 : Sparse (Fin 909) := [(0, (1 / 160)), (2, (-1 / 24)), (3, (-1 / 3)), (5, (1 / 8)), (6, (-1 / 32)), (9, (1 / 24)), (26, (-1 / 3)), (27, (-1 / 4)), (35, (-1 / 3)), (55, (1 / 2)), (68, (-1 / 4)), (238, (1 / 1)), (493, (1 / 1)), (727, (1 / 2))]

def value2474 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 12)), (2, (1 / 12)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 48)), (11, (-1 / 6)), (26, (-1 / 2)), (35, (-2 / 3)), (238, (1 / 2))]

def value2475 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 96)), (2, (29 / 96)), (3, (-1 / 6)), (5, (1 / 12)), (6, (1 / 16)), (9, (1 / 24)), (11, (-2 / 3)), (26, (-2 / 3)), (35, (-7 / 6)), (58, (-1 / 96)), (278, (-1 / 6)), (727, (1 / 2))]

def value2476 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 24)), (2, (-1 / 24)), (5, (1 / 4)), (6, (1 / 32)), (9, (1 / 12)), (27, (-1 / 8)), (58, (-1 / 96)), (68, (-1 / 8))]

def value2477 : Sparse (Fin 909) := [(2, (-1 / 16)), (5, (1 / 8)), (6, (5 / 96)), (9, (1 / 12)), (58, (-1 / 96)), (68, (-1 / 8))]

def value2478 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 8)), (2, (5 / 48)), (5, (1 / 8)), (6, (-1 / 32))]

def value2479 : Sparse (Fin 909) := [(0, (-1 / 48)), (2, (-1 / 48)), (5, (1 / 24)), (27, (-1 / 8))]

def value2480 : Sparse (Fin 909) := [(0, (-17 / 480)), (1, (3 / 8)), (2, (-1 / 12)), (5, (1 / 4)), (6, (-1 / 32)), (27, (-3 / 8))]

def value2481 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 32)), (2, (-11 / 288)), (5, (1 / 12)), (7, (-1 / 18)), (8, (-1 / 6)), (52, (-1 / 18)), (59, (1 / 6)), (75, (-1 / 2)), (428, (-1 / 2))]

def value2482 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 24)), (2, (-1 / 24)), (3, (-1 / 9)), (5, (1 / 72)), (33, (1 / 6)), (52, (-1 / 18)), (81, (1 / 6)), (428, (-1 / 2)), (760, (-1 / 2))]

def value2483 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 144)), (2, (-7 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (8, (-1 / 18)), (52, (-1 / 9)), (81, (1 / 6)), (86, (-1 / 2)), (855, (-1 / 2))]

def value2484 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 16)), (2, (-5 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-1 / 9)), (26, (-1 / 18)), (52, (-1 / 9)), (81, (2 / 3)), (228, (1 / 6))]

def value2485 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 18)), (5, (1 / 36)), (6, (-1 / 96)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-2 / 9)), (35, (-4 / 9)), (67, (-2 / 9))]

def value2486 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 288)), (2, (-1 / 96)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 6)), (8, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-2 / 9)), (855, (-1 / 2))]

def value2487 : Sparse (Fin 909) := [(57, (-1 / 2)), (86, (-1 / 2)), (855, (-1 / 1))]

def value2488 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 18)), (2, (-17 / 288)), (5, (1 / 12)), (6, (-1 / 288)), (8, (-1 / 9)), (52, (-1 / 9)), (85, (-1 / 2)), (86, (-1 / 2))]

def value2489 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (1 / 288)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (81, (1 / 6)), (855, (-1 / 2))]

def value2490 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 36)), (2, (-7 / 144)), (3, (-1 / 9)), (5, (1 / 12)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (81, (1 / 6))]

def value2491 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-7 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 18)), (81, (1 / 6)), (228, (1 / 6))]

def value2492 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 288)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 144)), (35, (-1 / 18))]

def value2493 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (1 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 6)), (67, (-1 / 18))]

def value2494 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (2, (1 / 32)), (3, (-1 / 6)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 6)), (26, (-1 / 9)), (35, (-2 / 9)), (52, (-1 / 18)), (67, (-1 / 18))]

def value2495 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-1 / 18))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2496 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 9)), (67, (-1 / 18)), (81, (1 / 6))]

def value2497 : Sparse (Fin 909) := [(3, (-1 / 9)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-2 / 9)), (52, (-1 / 18)), (67, (-1 / 18)), (81, (1 / 6)), (228, (1 / 6))]

def value2498 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-1 / 72)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 9)), (67, (-1 / 18))]

def value2499 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-11 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (81, (1 / 6)), (228, (1 / 6))]

def value2500 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 36)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-5 / 18)), (67, (-1 / 9))]

def value2501 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (5 / 72)), (2, (-5 / 288)), (3, (-1 / 6)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 6)), (35, (-1 / 9))]

def value2502 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 36)), (2, (-1 / 144)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 9))]

def value2503 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-1 / 36)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-1 / 18)), (8, (-1 / 9))]

def value2504 : Sparse (Fin 909) := [(1, (7 / 144)), (2, (-1 / 48)), (3, (-4 / 9)), (4, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 6)), (11, (-1 / 18)), (26, (-2 / 9)), (35, (-2 / 9)), (52, (-1 / 18)), (228, (1 / 6))]

def value2505 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (35, (-1 / 18))]

def value2506 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 144)), (2, (1 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (11, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 18)), (228, (1 / 6))]

def value2507 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 288)), (2, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (5 / 72)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 6))]

def value2508 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (228, (1 / 6))]

def value2509 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 18)), (2, (-7 / 288)), (3, (-1 / 18)), (31, (1 / 6)), (107, (-1 / 2)), (239, (-1 / 2))]

def value2510 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 24)), (2, (-1 / 32)), (3, (-1 / 18)), (8, (-1 / 18)), (40, (-1 / 2))]

def value2511 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (2, (-19 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (26, (-1 / 18))]

def value2512 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (7 / 96)), (2, (-5 / 144)), (3, (-2 / 9)), (4, (-1 / 9)), (26, (-1 / 18)), (57, (-1 / 2))]

def value2513 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 144)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 6)), (26, (-1 / 9)), (57, (-1 / 2)), (119, (-1 / 2))]

def value2514 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 9)), (31, (1 / 3)), (33, (1 / 6)), (119, (-1 / 2)), (204, (-1 / 2))]

def value2515 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 48)), (2, (-1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (31, (1 / 3)), (33, (2 / 3)), (51, (1 / 6)), (55, (1 / 6))]

def value2516 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (2, (-1 / 36)), (3, (-1 / 6)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (55, (1 / 6)), (64, (2 / 3)), (238, (1 / 3))]

def value2517 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 144)), (2, (1 / 288)), (3, (-4 / 9)), (4, (-1 / 18)), (13, (-1 / 18)), (26, (-2 / 9)), (34, (-2 / 9))]

def value2518 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 144)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 18)), (26, (-1 / 6)), (34, (-1 / 18)), (453, (-1 / 2)), (870, (-1 / 2))]

def value2519 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-1 / 48)), (3, (-5 / 18)), (13, (-5 / 18)), (26, (-1 / 6)), (34, (-2 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2520 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 16)), (2, (-7 / 144)), (5, (11 / 72)), (6, (-5 / 288)), (8, (-1 / 9)), (13, (-1 / 18)), (52, (-2 / 9)), (71, (-1 / 18)), (128, (-1 / 18)), (262, (1 / 6))]

def value2521 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (8, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (71, (-1 / 18)), (262, (1 / 6)), (870, (-1 / 2))]

def value2522 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 144)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 96)), (8, (-1 / 9)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (56, (1 / 6)), (870, (-1 / 2))]

def value2523 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 72)), (31, (1 / 6)), (51, (1 / 6)), (107, (-1 / 1)), (238, (1 / 3))]

def value2524 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-13 / 288)), (2, (-1 / 24)), (5, (1 / 9)), (6, (-1 / 72)), (8, (-1 / 18)), (52, (-1 / 18)), (798, (-1 / 2))]

def value2525 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 48)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 144)), (13, (-2 / 9)), (26, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 18)), (56, (1 / 6))]

def value2526 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (546, (-1 / 2))]

def value2527 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 144)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (26, (-1 / 6)), (204, (-1 / 2))]

def value2528 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 48)), (2, (-5 / 144)), (3, (-1 / 6)), (31, (1 / 6)), (52, (-1 / 18)), (204, (-1 / 2)), (237, (1 / 6)), (745, (-1 / 2))]

def value2529 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (8, (-1 / 18)), (52, (-1 / 18))]

def value2530 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 16)), (2, (1 / 72)), (3, (-1 / 9)), (4, (-1 / 18)), (26, (-1 / 18))]

def value2531 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (25 / 288)), (2, (-1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 18))]

def value2532 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 36)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (26, (-1 / 6))]

def value2533 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 72)), (2, (1 / 48)), (4, (-1 / 18)), (26, (-1 / 18))]

def value2534 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 36)), (2, (-1 / 144)), (3, (-1 / 9))]

def value2535 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 144)), (2, (1 / 96)), (3, (-1 / 18)), (13, (-1 / 9))]

def value2536 : Sparse (Fin 909) := [(0, (-19 / 1440)), (1, (5 / 72)), (2, (1 / 288)), (3, (-1 / 18))]

def value2537 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (17 / 288)), (2, (-5 / 288)), (3, (-1 / 3)), (4, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (31, (1 / 6)), (33, (1 / 6)), (34, (-1 / 18))]

def value2538 : Sparse (Fin 909) := [(3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 6)), (33, (1 / 6)), (34, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6))]

def value2539 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (-1 / 288)), (3, (-2 / 9)), (26, (-1 / 9)), (34, (-1 / 18))]

def value2540 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 24)), (2, (-1 / 36)), (3, (-2 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (26, (-1 / 18)), (33, (1 / 6)), (55, (1 / 6))]

def value2541 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (-1 / 72)), (3, (-1 / 18)), (4, (-1 / 18)), (26, (-1 / 18)), (31, (1 / 6)), (33, (1 / 6))]

def value2542 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-2 / 9)), (26, (-1 / 9))]

def value2543 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (13, (-1 / 9)), (26, (-1 / 18)), (34, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (64, (1 / 6)), (238, (1 / 6))]

def value2544 : Sparse (Fin 909) := [(2, (11 / 288)), (3, (-1 / 9)), (6, (-1 / 288)), (13, (-1 / 18)), (26, (-2 / 9)), (34, (-1 / 9)), (35, (-1 / 18))]

def value2545 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 48)), (3, (-5 / 18)), (4, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (34, (-1 / 9))]

def value2546 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (5 / 288)), (2, (1 / 72)), (3, (-2 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (13, (-1 / 9)), (26, (-1 / 9)), (34, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (55, (1 / 6)), (64, (1 / 6))]

def value2547 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2548 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (5 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (11, (-1 / 18)), (13, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 18))]

def value2549 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (1 / 144)), (5, (5 / 72)), (6, (1 / 144)), (8, (-1 / 18))]

def value2550 : Sparse (Fin 909) := [(0, (-23 / 1440)), (1, (1 / 8)), (2, (-1 / 96)), (3, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 9))]

def value2551 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (7 / 144)), (2, (-5 / 288)), (3, (-1 / 18))]

def value2552 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (29 / 288)), (2, (-1 / 288)), (3, (-4 / 9)), (4, (-2 / 9)), (12, (-2 / 9)), (13, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 18)), (55, (1 / 6))]

def value2553 : Sparse (Fin 909) := [(0, (-1 / 1440)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (24, (1 / 6))]

def value2554 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 6)), (52, (-1 / 18))]

def value2555 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 96)), (2, (-7 / 288)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18))]

def value2556 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (5 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6))]

def value2557 : Sparse (Fin 909) := [(1, (7 / 288)), (2, (-5 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (31, (1 / 6)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (238, (1 / 6))]

def value2558 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (13 / 144)), (2, (5 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18))]

def value2559 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (1 / 144)), (2, (-1 / 24)), (5, (1 / 36)), (8, (-1 / 6)), (30, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2624 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (33, (1 / 6))]

def value2625 : Sparse (Fin 909) := [(0, (-1 / 96)), (2, (-7 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (31, (1 / 6))]

def value2626 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 96)), (2, (-1 / 48)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2627 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 24)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (26, (-1 / 18))]

def value2628 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (5 / 72)), (2, (-1 / 72))]

def value2629 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (7 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (12, (-1 / 18))]

def value2630 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 96)), (2, (-1 / 72)), (4, (-1 / 18))]

def value2631 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (13 / 288)), (2, (-1 / 288)), (3, (-1 / 6)), (26, (-1 / 18))]

def value2632 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 6))]

def value2633 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (-1 / 72)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 18))]

def value2634 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 144)), (7, (-1 / 9)), (8, (-1 / 9))]

def value2635 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (13 / 144)), (2, (-1 / 72)), (3, (-1 / 9)), (12, (-1 / 9))]

def value2636 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 36)), (2, (1 / 24))]

def value2637 : Sparse (Fin 909) := [(0, (-29 / 1440)), (1, (7 / 72)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 6))]

def value2638 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 16)), (2, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2639 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (1 / 18)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 9))]

def value2640 : Sparse (Fin 909) := [(0, (-1 / 120)), (2, (-1 / 24))]

def value2641 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 72)), (2, (-7 / 96)), (3, (-1 / 6)), (5, (1 / 9)), (6, (-1 / 288)), (7, (-5 / 18)), (8, (-2 / 9)), (35, (-1 / 9))]

def value2642 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (19 / 288)), (4, (-1 / 18))]

def value2643 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-7 / 288)), (2, (-1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18))]

def value2644 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 72)), (3, (-1 / 9))]

def value2645 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (11 / 144))]

def value2646 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 16)), (2, (-11 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2647 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 72)), (2, (-1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18))]

def value2649 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (5, (1 / 3)), (6, (-1 / 24)), (8, (-1 / 2)), (24, (1 / 2)), (56, (1 / 1)), (71, (-1 / 3)), (197, (1 / 1))]

def value2650 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 48)), (2, (-3 / 16)), (5, (1 / 6)), (6, (-1 / 16)), (8, (-1 / 3)), (9, (1 / 6)), (56, (1 / 2)), (71, (-1 / 3)), (201, (1 / 1)), (796, (1 / 1)), (818, (1 / 2))]

def value2651 : Sparse (Fin 909) := [(0, (-1 / 48)), (1, (3 / 16)), (2, (-1 / 6)), (8, (-1 / 2)), (24, (1 / 2)), (30, (1 / 1))]

def value2652 : Sparse (Fin 909) := [(0, (-1 / 48)), (1, (1 / 16)), (2, (-1 / 8)), (3, (-1 / 3)), (4, (-1 / 3)), (5, (1 / 12)), (8, (-1 / 3)), (24, (1 / 1)), (27, (-1 / 4)), (30, (1 / 2)), (56, (1 / 2))]

def value2653 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 24)), (2, (-1 / 12)), (5, (1 / 12)), (27, (-1 / 4)), (31, (1 / 2)), (51, (1 / 1)), (124, (1 / 2)), (126, (1 / 1)), (236, (1 / 2))]

def value2654 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 32)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 48)), (13, (-1 / 6)), (52, (-1 / 3)), (55, (1 / 2)), (69, (-1 / 6)), (71, (-1 / 6)), (125, (1 / 2)), (197, (1 / 2))]

def value2655 : Sparse (Fin 909) := [(0, (-1 / 48)), (1, (3 / 16)), (2, (-1 / 8)), (5, (1 / 24)), (8, (-1 / 3)), (30, (1 / 2))]

def value2656 : Sparse (Fin 909) := [(0, (-7 / 240)), (1, (7 / 32)), (2, (-17 / 96)), (3, (-1 / 3)), (4, (-1 / 6)), (5, (1 / 12)), (7, (-1 / 6)), (8, (-1 / 6)), (24, (1 / 2)), (27, (-3 / 8)), (30, (1 / 2)), (31, (1 / 2)), (51, (1 / 2))]

def value2657 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (1 / 96)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 48)), (8, (-1 / 6)), (13, (-1 / 3)), (26, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 6)), (56, (1 / 2))]

def value2658 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 6)), (2, (-3 / 16)), (3, (-1 / 6)), (5, (5 / 24)), (6, (-5 / 96)), (8, (-1 / 6)), (13, (-1 / 6)), (35, (-1 / 6)), (52, (-2 / 3)), (82, (-1 / 6)), (128, (-1 / 3)), (201, (1 / 2))]

def value2659 : Sparse (Fin 909) := [(0, (-5 / 96)), (1, (3 / 8)), (2, (-7 / 32)), (3, (-2 / 3)), (4, (-1 / 2)), (5, (1 / 24)), (27, (-1 / 8)), (31, (1 / 1)), (51, (1 / 2)), (52, (-1 / 6))]

def value2660 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (3 / 8)), (2, (-3 / 32)), (3, (-1 / 6)), (4, (-1 / 3))]

def value2661 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 12)), (2, (-11 / 96)), (3, (-5 / 6)), (4, (-1 / 6)), (5, (1 / 24)), (12, (-1 / 3)), (13, (-1 / 6)), (27, (-1 / 8)), (31, (1 / 2)), (51, (1 / 2)), (52, (-1 / 6))]

def value2662 : Sparse (Fin 909) := [(0, (-1 / 15)), (1, (5 / 32)), (2, (-5 / 96)), (3, (-2 / 3)), (4, (-1 / 3)), (12, (-1 / 3)), (13, (-1 / 6))]

def value2663 : Sparse (Fin 909) := [(0, (1 / 240)), (2, (-5 / 48)), (3, (-1 / 2)), (5, (1 / 8)), (7, (-1 / 6)), (8, (-1 / 6)), (12, (-1 / 6)), (23, (1 / 2)), (24, (1 / 2)), (27, (-1 / 4)), (55, (1 / 2))]

def value2666 : Sparse (Fin 909) := [(0, (-7 / 240)), (1, (13 / 96)), (2, (-5 / 96)), (3, (-5 / 6)), (4, (-1 / 3)), (12, (-1 / 3)), (26, (-1 / 6))]

def value2667 : Sparse (Fin 909) := [(0, (-11 / 240)), (1, (25 / 48)), (2, (-1 / 8)), (3, (-2 / 3)), (4, (-2 / 3)), (12, (-1 / 6)), (31, (1 / 1))]

def value2668 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (5 / 24)), (2, (-1 / 12)), (3, (-1 / 2)), (4, (-1 / 3)), (5, (1 / 24)), (12, (-1 / 6)), (27, (-1 / 4)), (31, (1 / 1)), (51, (1 / 1)), (55, (1 / 2))]

def value2669 : Sparse (Fin 909) := [(0, (-7 / 160)), (1, (35 / 96)), (2, (-1 / 16)), (3, (-2 / 3)), (4, (-1 / 2)), (26, (-1 / 6)), (31, (1 / 2))]

def value2670 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (5 / 24)), (6, (-1 / 32)), (9, (1 / 24)), (13, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 6)), (55, (1 / 2)), (68, (-1 / 4)), (237, (1 / 1)), (494, (1 / 1)), (728, (1 / 2))]

def value2671 : Sparse (Fin 909) := [(0, (-1 / 48)), (1, (35 / 96)), (2, (1 / 24)), (3, (-7 / 6)), (4, (-2 / 3)), (5, (1 / 24)), (6, (-1 / 96)), (26, (-2 / 3)), (35, (-1 / 6)), (55, (1 / 2))]

def value2672 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 96)), (2, (-3 / 32)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 24)), (9, (1 / 12)), (35, (-1 / 6)), (52, (-1 / 2)), (55, (1 / 2)), (228, (1 / 1)), (727, (1 / 2)), (728, (1 / 2))]

def value2673 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (3 / 32)), (5, (-1 / 8)), (6, (1 / 32)), (9, (5 / 24)), (58, (-1 / 96))]

def value2674 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (1 / 48)), (5, (1 / 12)), (6, (-1 / 96)), (27, (-1 / 8))]

def value2675 : Sparse (Fin 909) := [(0, (17 / 240)), (1, (1 / 8)), (2, (-1 / 48))]

def value2676 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 48)), (2, (-1 / 48)), (3, (-1 / 9)), (12, (-1 / 6)), (13, (-1 / 9))]

def value2677 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 36)), (13, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (60, (-1 / 9))]

def value2678 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 12)), (2, (-25 / 288)), (5, (11 / 72)), (6, (-5 / 288)), (8, (-1 / 9)), (52, (-1 / 9)), (315, (-1 / 2))]

def value2679 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 16)), (5, (5 / 72)), (6, (1 / 96)), (52, (-1 / 18)), (71, (-1 / 18)), (764, (-1 / 2))]

def value2680 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 144)), (5, (-1 / 18)), (6, (-1 / 96)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (71, (-1 / 18)), (507, (-1 / 2))]

def value2681 : Sparse (Fin 909) := [(3, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (59, (1 / 6)), (60, (-1 / 18)), (82, (-1 / 9)), (128, (-1 / 6)), (199, (1 / 6))]

def value2682 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (1 / 144)), (5, (1 / 24)), (6, (-1 / 288)), (13, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 9)), (60, (-1 / 9)), (82, (-1 / 18)), (128, (-1 / 9))]

def value2683 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (2, (-11 / 288)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 6)), (8, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 6)), (59, (1 / 6)), (82, (-1 / 18)), (199, (1 / 6))]

def value2684 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 6)), (60, (-1 / 18)), (82, (-1 / 18)), (128, (-1 / 18)), (201, (1 / 6))]

def value2685 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 24)), (2, (-7 / 144)), (5, (5 / 72)), (6, (-1 / 96)), (8, (-1 / 18)), (52, (-1 / 18))]

def value2686 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-13 / 288)), (3, (-5 / 18)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 6)), (52, (-1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (201, (1 / 6))]

def value2687 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 288)), (3, (-1 / 18)), (5, (-1 / 72)), (6, (-1 / 144)), (13, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6)), (82, (-1 / 18)), (199, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2688 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (56, (1 / 6)), (201, (1 / 6))]

def value2689 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (12, (-1 / 18)), (13, (-2 / 9)), (82, (-1 / 18)), (128, (-1 / 18)), (201, (1 / 6))]

def value2690 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144))]

def value2691 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (12, (-1 / 6)), (13, (-7 / 18)), (35, (-1 / 6)), (52, (-1 / 9)), (54, (1 / 6)), (82, (-1 / 9)), (128, (-1 / 9)), (199, (1 / 6))]

def value2692 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (5 / 72)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 18)), (52, (-2 / 9)), (82, (-1 / 18)), (128, (-1 / 9))]

def value2693 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 144)), (2, (-11 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 72)), (8, (-1 / 18)), (13, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (56, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (201, (1 / 6))]

def value2694 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (5 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-5 / 288)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-2 / 9)), (54, (1 / 6)), (82, (-1 / 18)), (199, (1 / 6))]

def value2695 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (-5 / 96)), (5, (1 / 72)), (6, (-1 / 72)), (26, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (226, (1 / 6))]

def value2696 : Sparse (Fin 909) := [(3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-2 / 9)), (26, (-1 / 18)), (33, (1 / 6)), (34, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6))]

def value2697 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 144)), (3, (-5 / 18)), (13, (-1 / 9)), (34, (-1 / 18))]

def value2698 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (13, (-1 / 6)), (26, (-1 / 9)), (34, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2699 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (7 / 144)), (2, (-5 / 288)), (3, (-5 / 18)), (12, (-1 / 18)), (26, (-1 / 9)), (34, (-1 / 9))]

def value2700 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (1 / 72)), (5, (1 / 36)), (6, (-1 / 288)), (8, (-1 / 18))]

def value2701 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18))]

def value2702 : Sparse (Fin 909) := [(3, (-2 / 9)), (4, (-1 / 18)), (13, (-1 / 18)), (26, (-2 / 9)), (34, (-1 / 18)), (35, (-1 / 18)), (56, (1 / 6))]

def value2703 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (13 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (26, (-1 / 18)), (34, (-1 / 18))]

def value2704 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (1 / 288)), (3, (-1 / 18))]

def value2705 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (1 / 36)), (2, (-1 / 96)), (3, (-1 / 18))]

def value2706 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 72)), (2, (-1 / 144)), (3, (-7 / 18)), (4, (-5 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 18)), (56, (1 / 6))]

def value2707 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (56, (1 / 6))]

def value2708 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144))]

def value2709 : Sparse (Fin 909) := [(1, (25 / 288)), (2, (-1 / 96)), (3, (-7 / 18)), (4, (-1 / 9)), (12, (-2 / 9)), (13, (-1 / 6)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6))]

def value2710 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 144)), (2, (1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (13, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6))]

def value2711 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (1 / 72)), (2, (-1 / 48)), (8, (-1 / 18)), (30, (1 / 6)), (208, (-1 / 2)), (253, (-1 / 2))]

def value2712 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 18)), (2, (-5 / 144)), (5, (1 / 72)), (27, (-1 / 24)), (208, (-1 / 1))]

def value2713 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 288)), (2, (1 / 36)), (3, (-1 / 9)), (5, (1 / 24)), (52, (-1 / 9)), (89, (-1 / 2))]

def value2714 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (1 / 72)), (2, (-1 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (8, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 9)), (123, (1 / 6))]

def value2715 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (59, (1 / 6))]

def value2716 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (81, (1 / 6))]

def value2717 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (-1 / 36)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 18)), (33, (1 / 6))]

def value2718 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 32)), (2, (-1 / 48)), (3, (-1 / 6)), (12, (-1 / 9)), (13, (-1 / 9)), (33, (1 / 6))]

def value2719 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (26, (-1 / 18)), (33, (1 / 6)), (51, (1 / 6))]

def value2720 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 144)), (2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 288)), (7, (-1 / 18))]

def value2721 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (-1 / 96)), (7, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2722 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (2, (1 / 72)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6))]

def value2723 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-5 / 96)), (2, (-23 / 288)), (3, (-1 / 18)), (5, (11 / 72)), (6, (-1 / 96)), (7, (-2 / 9)), (8, (-5 / 18)), (35, (-1 / 18))]

def value2724 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (5 / 96)), (2, (-1 / 144)), (4, (-1 / 18))]

def value2725 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (5 / 288)), (4, (-1 / 18))]

def value2726 : Sparse (Fin 909) := [(1, (1 / 18)), (2, (1 / 72)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 72)), (26, (-1 / 18)), (55, (1 / 6))]

def value2727 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (11 / 288)), (2, (1 / 96)), (3, (-1 / 6)), (26, (-1 / 18))]

def value2728 : Sparse (Fin 909) := [(1, (7 / 144)), (2, (-1 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18))]

def value2729 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 96)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (55, (1 / 6))]

def value2730 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 36)), (2, (1 / 144)), (5, (1 / 72)), (6, (-1 / 288))]

def value2731 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (13 / 288)), (2, (-1 / 24)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18))]

def value2732 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (17 / 288)), (2, (-1 / 144)), (3, (-1 / 3)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 18)), (55, (1 / 6))]

def value2733 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (-13 / 288)), (3, (-1 / 6)), (5, (7 / 72)), (6, (-1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 6)), (228, (1 / 6))]

def value2734 : Sparse (Fin 909) := [(0, (23 / 720)), (2, (-1 / 144))]

def value2735 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (5 / 144)), (2, (7 / 288)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-2 / 9)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6))]

def value2736 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 36)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 18)), (9, (1 / 36)), (69, (-1 / 18)), (71, (-1 / 18))]

def value2737 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 72)), (2, (-1 / 72)), (5, (-1 / 36)), (6, (-1 / 144))]

def value2738 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 24)), (2, (-1 / 16)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (52, (-1 / 9))]

def value2739 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (5 / 288)), (3, (-1 / 18)), (5, (-1 / 72)), (6, (-1 / 288)), (7, (1 / 9)), (8, (-1 / 18)), (35, (-1 / 18))]

def value2740 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (5 / 288)), (3, (1 / 9)), (12, (-1 / 18)), (13, (-1 / 18))]

def value2741 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (1 / 9)), (5, (1 / 72)), (7, (1 / 9)), (26, (-1 / 18)), (35, (1 / 18)), (52, (-1 / 18)), (67, (-1 / 18))]

def value2742 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 16)), (2, (1 / 144)), (3, (1 / 9)), (4, (-1 / 18)), (26, (-1 / 18))]

def value2743 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (11 / 288)), (2, (-1 / 72)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18))]

def value2744 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 72)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (1 / 9))]

def value2745 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (1 / 9))]

def value2746 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (13, (-1 / 9)), (52, (-1 / 18))]

def value2747 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 72)), (2, (-1 / 144)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (1 / 9))]

def value2748 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (5 / 144)), (2, (11 / 288)), (3, (-1 / 18))]

def value2749 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 9)), (35, (-1 / 9))]

def value2750 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 144)), (2, (-1 / 48)), (3, (-1 / 9)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2751 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 6)), (8, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 9)), (67, (-1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2752 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 12)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (25, (1 / 6))]

def value2753 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-5 / 288)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (34, (-1 / 18)), (51, (1 / 6)), (64, (1 / 6))]

def value2754 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2755 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 24)), (5, (1 / 18)), (7, (-1 / 9)), (8, (-1 / 9))]

def value2756 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 36))]

def value2757 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 18)), (52, (-1 / 18))]

def value2758 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (7 / 144)), (2, (-1 / 288)), (3, (-1 / 18)), (12, (-1 / 18))]

def value2759 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 72)), (12, (-1 / 18))]

def value2760 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 144)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6))]

def value2761 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (11 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 9))]

def value2762 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6))]

def value2763 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (13, (1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2764 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 9)), (13, (-2 / 9))]

def value2765 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 144)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 144)), (26, (-1 / 18)), (35, (-1 / 9)), (238, (1 / 6))]

def value2766 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 18)), (5, (1 / 36)), (6, (1 / 72)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (1 / 9))]

def value2767 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (7 / 144)), (2, (-1 / 36)), (3, (-1 / 9))]

def value2768 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 6)), (35, (-1 / 18))]

def value2769 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (13 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (12, (-1 / 9))]

def value2770 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (1 / 144)), (3, (-1 / 9)), (5, (1 / 72)), (13, (-1 / 9)), (35, (-1 / 18))]

def value2771 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (3, (-2 / 9)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (54, (1 / 6))]

def value2772 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-5 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (26, (-1 / 18)), (52, (-1 / 18))]

def value2773 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (1 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (26, (1 / 9)), (35, (-1 / 18))]

def value2774 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 72)), (2, (1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2775 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 48)), (2, (-5 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 3))]

def value2776 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-1 / 96)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 6)), (26, (-1 / 18))]

def value2777 : Sparse (Fin 909) := [(1, (7 / 144)), (2, (1 / 144)), (3, (1 / 9)), (5, (1 / 72)), (52, (-1 / 18))]

def value2778 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-1 / 48)), (4, (-1 / 9)), (12, (-1 / 18))]

def value2779 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2780 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 144))]

def value2781 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 36))]

def value2782 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 6)), (26, (-1 / 9)), (35, (-1 / 9))]

def value2783 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (7 / 144)), (2, (-1 / 144))]

def value2784 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-1 / 12)), (2, (-1 / 144))]

def value2785 : Sparse (Fin 909) := [(0, (19 / 360)), (1, (1 / 72))]

def value2786 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-1 / 288)), (3, (-1 / 6))]

def value2787 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (5 / 32)), (6, (1 / 24)), (9, (1 / 24)), (13, (-1 / 3)), (35, (-2 / 3)), (70, (-1 / 3)), (196, (1 / 2))]

def value2788 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 12)), (2, (-1 / 12)), (3, (-1 / 3)), (5, (1 / 8)), (6, (-1 / 32)), (7, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 3)), (35, (-1 / 3)), (54, (1 / 2))]

def value2789 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (1 / 4)), (5, (-1 / 12)), (6, (1 / 12)), (7, (-1 / 3)), (35, (-2 / 3)), (82, (-1 / 3)), (199, (1 / 2))]

def value2790 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 96)), (2, (-1 / 16)), (3, (-2 / 3)), (5, (1 / 12)), (6, (-1 / 96)), (12, (-1 / 6)), (13, (-2 / 3)), (35, (-1 / 6)), (52, (-1 / 3))]

def value2791 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 3)), (2, (1 / 12)), (3, (-2 / 3)), (12, (-1 / 6)), (13, (-2 / 3))]

def value2792 : Sparse (Fin 909) := [(0, (23 / 120)), (1, (3 / 8)), (12, (-1 / 6))]

def value2793 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 24)), (2, (-1 / 48)), (3, (-2 / 3)), (5, (1 / 24)), (6, (-1 / 96)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 3)), (35, (-1 / 6)), (55, (1 / 2))]

def value2795 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 16)), (2, (1 / 16)), (3, (-2 / 3)), (4, (-1 / 3)), (25, (1 / 2)), (26, (-1 / 3))]

def value2796 : Sparse (Fin 909) := [(0, (7 / 120)), (1, (3 / 8)), (4, (-1 / 3))]

def value2797 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (1 / 8)), (2, (1 / 24)), (5, (1 / 8)), (6, (-1 / 32))]

def value2799 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 8)), (2, (1 / 6)), (5, (-1 / 4)), (6, (1 / 16))]

def value2800 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (1 / 6)), (2, (-1 / 24))]

def value2801 : Sparse (Fin 909) := [(0, (1 / 30)), (1, (-1 / 8)), (2, (1 / 24))]

def value2802 : Sparse (Fin 909) := [(2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 3)), (8, (-1 / 18)), (35, (-1 / 6)), (67, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2803 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 72)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18))]

def value2804 : Sparse (Fin 909) := [(3, (-1 / 6)), (26, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 18)), (67, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2805 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 24)), (2, (-1 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (25, (1 / 6)), (26, (-1 / 18))]

def value2806 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 24)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 18)), (24, (1 / 6)), (26, (-1 / 18))]

def value2807 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-1 / 24)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2808 : Sparse (Fin 909) := [(1, (5 / 288)), (2, (1 / 72)), (3, (-1 / 18)), (5, (-1 / 36)), (6, (-1 / 288)), (7, (1 / 9)), (35, (1 / 9)), (52, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2809 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (8, (1 / 9)), (71, (-1 / 9))]

def value2810 : Sparse (Fin 909) := [(0, (-1 / 360)), (3, (1 / 9)), (5, (1 / 72)), (7, (-1 / 18))]

def value2811 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 48)), (2, (1 / 36)), (5, (1 / 72)), (8, (-1 / 18))]

def value2812 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 144)), (2, (-7 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 9))]

def value2813 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 36)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18))]

def value2814 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 144)), (2, (-1 / 36)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 9))]

def value2815 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 72)), (9, (1 / 72)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 6)), (69, (-1 / 18))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1408 : Sparse (Fin 909) := [(1, (5 / 48)), (2, (5 / 48)), (3, (-1 / 2)), (13, (-1 / 6)), (26, (-1 / 1)), (34, (-1 / 2)), (35, (-1 / 2)), (54, (3 / 2)), (65, (3 / 2)), (67, (-1 / 2)), (257, (-1 / 6)), (264, (1 / 1)), (266, (3 / 2))]

def value1409 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (5 / 96)), (2, (-1 / 96)), (3, (-1 / 1)), (13, (-1 / 2)), (26, (-1 / 2)), (33, (3 / 2)), (35, (-1 / 6)), (54, (3 / 2)), (62, (1 / 1))]

def value1410 : Sparse (Fin 909) := [(0, (3 / 160)), (1, (1 / 32)), (2, (-1 / 12)), (3, (-3 / 2)), (12, (-1 / 1)), (13, (-17 / 6)), (32, (-1 / 3))]

def value1411 : Sparse (Fin 909) := [(0, (1 / 160)), (2, (-5 / 96)), (3, (-3 / 2)), (12, (-1 / 2)), (13, (-7 / 3)), (26, (-1 / 2)), (32, (-1 / 3)), (34, (-1 / 1)), (60, (-1 / 2)), (61, (3 / 2))]

def value1412 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 96)), (2, (1 / 48)), (3, (-2 / 3)), (12, (-1 / 3)), (13, (-1 / 1)), (26, (-1 / 3)), (32, (-1 / 6)), (34, (-1 / 3)), (35, (-1 / 2)), (54, (1 / 2)), (55, (1 / 1)), (60, (-1 / 3)), (61, (1 / 1)), (65, (1 / 2)), (67, (-1 / 6)), (257, (-1 / 6)), (264, (1 / 2)), (266, (1 / 1)), (268, (1 / 1))]

def value1413 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 32)), (2, (-5 / 96)), (3, (-4 / 3)), (4, (-1 / 6)), (12, (-2 / 3)), (13, (-5 / 3)), (26, (-1 / 6)), (32, (-1 / 6)), (33, (1 / 2)), (34, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 6)), (54, (1 / 1)), (56, (1 / 2)), (60, (-1 / 6)), (61, (1 / 2)), (62, (1 / 2))]

def value1414 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (3 / 32)), (2, (3 / 32)), (3, (-2 / 3)), (6, (-1 / 96)), (7, (-1 / 3)), (12, (-1 / 6)), (13, (-1 / 2)), (26, (-1 / 2)), (34, (-1 / 3)), (35, (-5 / 6)), (55, (1 / 2)), (60, (-1 / 6)), (67, (-1 / 3)), (70, (-1 / 6)), (197, (1 / 2)), (257, (-1 / 6)), (268, (1 / 2))]

def value1415 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 96)), (2, (1 / 48)), (3, (-1 / 3)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 1)), (25, (1 / 2)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 6)), (54, (1 / 1)), (55, (1 / 1)), (63, (1 / 1)), (64, (1 / 2)), (65, (1 / 1)), (125, (1 / 2)), (196, (1 / 2)), (264, (1 / 2)), (266, (1 / 2))]

def value1416 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (11 / 96)), (3, (-3 / 2)), (4, (-1 / 3)), (7, (-2 / 3)), (13, (-1 / 6)), (26, (-4 / 3)), (34, (-1 / 2)), (35, (-7 / 6)), (55, (1 / 2)), (64, (1 / 1)), (67, (-2 / 3)), (70, (-1 / 6)), (125, (1 / 2)), (257, (-1 / 6)), (266, (1 / 2))]

def value1417 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (7 / 96)), (2, (7 / 96)), (3, (-4 / 3)), (7, (-1 / 6)), (12, (-1 / 2)), (13, (-1 / 1)), (23, (1 / 2)), (26, (-2 / 3)), (34, (-1 / 3)), (35, (-1 / 2)), (55, (1 / 1)), (63, (1 / 2)), (65, (1 / 2)), (67, (-1 / 6))]

def value1418 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (1 / 24)), (2, (-7 / 96)), (3, (-1 / 1)), (12, (-1 / 3)), (13, (-1 / 2)), (25, (1 / 2)), (26, (-1 / 6)), (33, (3 / 2)), (35, (-1 / 6)), (55, (1 / 1)), (63, (1 / 2)), (64, (1 / 1))]

def value1419 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 32)), (2, (-1 / 32)), (3, (-5 / 3)), (4, (-2 / 3)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (24, (1 / 2)), (26, (-1 / 1)), (33, (1 / 2)), (34, (-1 / 3)), (35, (-1 / 3)), (55, (3 / 2)), (64, (1 / 2)), (66, (1 / 2)), (67, (-1 / 6))]

def value1420 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 48)), (2, (-1 / 32)), (3, (-7 / 6)), (4, (-1 / 3)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 2)), (25, (1 / 1)), (26, (-2 / 3)), (33, (1 / 1)), (34, (-1 / 3)), (35, (-1 / 6)), (55, (1 / 2)), (63, (1 / 1)), (64, (1 / 1)), (65, (1 / 2)), (67, (-1 / 6))]

def value1421 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-11 / 96)), (6, (-1 / 96)), (13, (-1 / 1)), (35, (-1 / 3)), (63, (1 / 2))]

def value1422 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 96)), (2, (5 / 96)), (3, (-2 / 3)), (5, (1 / 24)), (6, (-1 / 48)), (7, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 3)), (34, (-1 / 3)), (35, (-2 / 3)), (67, (-1 / 3))]

def value1423 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 48)), (3, (-1 / 6)), (5, (1 / 24)), (13, (-1 / 3)), (26, (-1 / 6)), (33, (1 / 2)), (34, (-1 / 6)), (52, (-1 / 6)), (55, (1 / 2)), (64, (1 / 2))]

def value1424 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-5 / 6)), (5, (1 / 8)), (6, (-1 / 48)), (7, (-1 / 3)), (13, (-1 / 3)), (26, (-2 / 3)), (34, (-2 / 3)), (35, (-3 / 2)), (52, (-2 / 3)), (60, (-2 / 3)), (67, (-2 / 3)), (128, (-1 / 6)), (271, (1 / 2)), (275, (1 / 1)), (276, (-1 / 2))]

def value1425 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (7 / 96)), (2, (-1 / 24)), (3, (-11 / 6)), (4, (-1 / 3)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 6)), (13, (-2 / 3)), (26, (-4 / 3)), (34, (-5 / 6)), (35, (-1 / 2)), (52, (-1 / 6)), (64, (1 / 2)), (67, (-1 / 3))]

def value1426 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 32)), (2, (1 / 24)), (3, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 6)), (33, (1 / 2)), (34, (-1 / 3)), (35, (-1 / 6)), (54, (1 / 2)), (65, (1 / 2)), (67, (-1 / 6))]

def value1427 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 48)), (2, (1 / 24)), (3, (-5 / 6)), (12, (-1 / 6)), (13, (-1 / 3)), (26, (-1 / 6)), (33, (1 / 2))]

def value1428 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 32)), (2, (1 / 48)), (3, (-1 / 2)), (12, (-1 / 3)), (13, (-5 / 6)), (26, (-1 / 3)), (34, (-1 / 3))]

def value1429 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 8)), (2, (-1 / 32)), (3, (-3 / 2)), (4, (-2 / 3)), (13, (-1 / 6)), (26, (-7 / 6)), (34, (-1 / 2)), (35, (-1 / 6)), (56, (1 / 2)), (66, (1 / 2)), (67, (-1 / 6))]

def value1430 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (3 / 32)), (2, (-5 / 96)), (3, (-4 / 3)), (4, (-2 / 3)), (13, (-1 / 6)), (26, (-1 / 1)), (34, (-1 / 3))]

def value1431 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (3 / 16)), (2, (-1 / 24)), (3, (-13 / 6)), (4, (-2 / 3)), (12, (-2 / 3)), (13, (-1 / 1)), (26, (-1 / 1)), (33, (1 / 1)), (34, (-2 / 3)), (35, (-1 / 6)), (54, (1 / 2)), (65, (1 / 2)), (67, (-1 / 6))]

def value1432 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (23 / 96)), (2, (-11 / 96)), (3, (-2 / 1)), (4, (-1 / 3)), (12, (-1 / 1)), (13, (-7 / 6)), (26, (-1 / 3)), (33, (1 / 1)), (34, (-1 / 3))]

def value1433 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (-1 / 24)), (3, (-2 / 1)), (4, (-2 / 3)), (13, (-1 / 3)), (26, (-2 / 1)), (34, (-4 / 3)), (65, (1 / 2)), (66, (1 / 1)), (67, (-1 / 2))]

def value1434 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (9 / 32)), (2, (-13 / 96)), (3, (-13 / 6)), (4, (-1 / 1)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-7 / 6)), (33, (1 / 2)), (34, (-1 / 3))]

def value1435 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 32)), (2, (-5 / 96)), (3, (-1 / 1)), (12, (-1 / 2)), (13, (-3 / 2)), (26, (-1 / 6)), (32, (-1 / 6)), (33, (1 / 2)), (34, (-1 / 3)), (35, (-1 / 6)), (55, (1 / 2)), (60, (-1 / 6)), (61, (1 / 2))]

def value1436 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (3 / 32)), (2, (-1 / 16)), (3, (-1 / 1)), (5, (1 / 6)), (7, (-2 / 1)), (9, (1 / 24)), (35, (-4 / 3)), (69, (-1 / 1)), (70, (-4 / 3)), (277, (3 / 2)), (278, (-1 / 2))]

def value1437 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-7 / 32)), (2, (-29 / 96)), (5, (3 / 4)), (6, (-3 / 32)), (7, (-1 / 2)), (8, (-1 / 1)), (9, (3 / 8)), (58, (-1 / 96)), (69, (-1 / 1)), (70, (-1 / 3)), (71, (-2 / 1))]

def value1438 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 48)), (2, (-11 / 48)), (5, (5 / 8)), (6, (-1 / 16)), (7, (-1 / 2)), (8, (-1 / 1)), (9, (1 / 6)), (69, (-1 / 1)), (70, (-1 / 3)), (71, (-2 / 1))]

def value1439 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (5, (-1 / 72)), (6, (-1 / 72)), (7, (-1 / 18)), (9, (1 / 9)), (69, (-1 / 6)), (70, (-1 / 18)), (71, (-1 / 9)), (277, (1 / 6))]

def value1440 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 6)), (8, (-1 / 9)), (9, (1 / 36)), (35, (-1 / 18)), (69, (-1 / 9)), (71, (-1 / 9)), (256, (1 / 3)), (277, (1 / 6))]

def value1441 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (5, (1 / 18)), (6, (-1 / 72)), (7, (-1 / 6)), (9, (1 / 12)), (35, (-1 / 18)), (69, (-2 / 9)), (70, (-1 / 9)), (71, (-1 / 9)), (726, (1 / 6))]

def value1442 : Sparse (Fin 909) := [(2, (-1 / 36)), (5, (1 / 12)), (7, (-2 / 9)), (8, (-1 / 18)), (69, (-7 / 18)), (70, (-2 / 9)), (71, (-1 / 6)), (256, (1 / 6))]

def value1443 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 288)), (2, (-7 / 144)), (5, (1 / 9)), (6, (-5 / 288)), (8, (-2 / 9)), (9, (1 / 12)), (69, (-1 / 18)), (71, (-7 / 18)), (818, (1 / 6))]

def value1444 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (2, (-1 / 36)), (5, (1 / 12)), (7, (-1 / 18)), (8, (-2 / 9)), (69, (-1 / 6)), (71, (-11 / 18)), (256, (1 / 6))]

def value1445 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 18)), (7, (-2 / 9)), (8, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (69, (-1 / 9)), (70, (-1 / 18)), (71, (-1 / 18)), (256, (1 / 6)), (280, (-1 / 2)), (726, (1 / 6))]

def value1446 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 9)), (35, (-1 / 18)), (69, (-2 / 9)), (70, (-1 / 6)), (71, (-1 / 18)), (256, (1 / 6)), (277, (1 / 6)), (279, (-1 / 2))]

def value1447 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 6)), (8, (-1 / 9)), (35, (-1 / 18)), (69, (-1 / 6)), (70, (-1 / 18)), (71, (-2 / 9)), (256, (1 / 6)), (277, (1 / 6)), (280, (-1 / 2))]

def value1448 : Sparse (Fin 909) := [(3, (-1 / 18)), (7, (-1 / 9)), (35, (-2 / 9)), (52, (-1 / 9)), (256, (1 / 3)), (277, (1 / 6)), (279, (-1 / 2)), (726, (1 / 6))]

def value1449 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (256, (1 / 3)), (277, (1 / 6)), (280, (-1 / 2)), (818, (1 / 6))]

def value1450 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (-1 / 32)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 96)), (8, (-1 / 18)), (9, (1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (69, (-1 / 18)), (71, (-1 / 6)), (256, (1 / 3)), (726, (1 / 6)), (818, (1 / 6))]

def value1451 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 48)), (5, (1 / 18)), (8, (-1 / 6)), (69, (-1 / 9)), (71, (-5 / 9)), (280, (-1 / 2))]

def value1452 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (2, (-1 / 32)), (5, (1 / 12)), (7, (-1 / 9)), (8, (-2 / 9)), (69, (-2 / 9)), (70, (-1 / 18)), (71, (-7 / 18)), (281, (-1 / 2))]

def value1453 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 36)), (5, (1 / 9)), (6, (-1 / 72)), (7, (-1 / 9)), (9, (1 / 18)), (52, (-1 / 9)), (69, (-1 / 9)), (70, (-1 / 9)), (256, (1 / 3)), (818, (1 / 3))]

def value1454 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (-1 / 288)), (5, (-1 / 72)), (51, (1 / 6)), (59, (1 / 6)), (69, (-1 / 18)), (71, (-1 / 18)), (256, (1 / 6))]

def value1455 : Sparse (Fin 909) := [(2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (59, (1 / 6)), (69, (-1 / 9)), (70, (-1 / 9)), (256, (1 / 6)), (287, (-1 / 2))]

def value1456 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (-1 / 18)), (3, (-1 / 18)), (5, (7 / 72)), (7, (-1 / 18)), (8, (-1 / 6)), (13, (-1 / 18)), (52, (-1 / 9)), (59, (1 / 3)), (201, (1 / 6)), (256, (1 / 6)), (818, (1 / 6))]

def value1457 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 288)), (5, (-5 / 72)), (6, (-1 / 144)), (55, (1 / 6)), (228, (1 / 3)), (282, (-1 / 2)), (726, (1 / 6))]

def value1458 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (-1 / 36)), (6, (-1 / 288)), (7, (-1 / 6)), (8, (-1 / 9)), (10, (1 / 6)), (27, (-1 / 24)), (35, (-1 / 18))]

def value1459 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 3)), (59, (1 / 3))]

def value1460 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 18)), (23, (1 / 6)), (35, (-1 / 9)), (54, (1 / 3)), (72, (-1 / 2)), (199, (1 / 6))]

def value1461 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 48)), (3, (-2 / 9)), (5, (1 / 36)), (24, (1 / 6)), (35, (-1 / 9)), (73, (-1 / 2))]

def value1462 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 24)), (2, (-1 / 36)), (5, (1 / 18)), (8, (-1 / 18)), (24, (1 / 6)), (56, (1 / 3)), (74, (-1 / 2)), (201, (1 / 6))]

def value1463 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (7, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (54, (1 / 6)), (199, (1 / 6)), (228, (1 / 6)), (286, (-1 / 2)), (726, (1 / 6))]

def value1464 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (5, (1 / 36)), (7, (1 / 18)), (8, (-1 / 18)), (77, (-1 / 2)), (286, (-1 / 2)), (287, (-1 / 2))]

def value1465 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 18)), (6, (-1 / 288)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (56, (1 / 6)), (201, (1 / 6)), (228, (1 / 6)), (288, (-1 / 2)), (726, (1 / 6))]

def value1466 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 96)), (5, (1 / 36)), (7, (-1 / 18)), (8, (1 / 18)), (78, (-1 / 2)), (288, (-1 / 2)), (289, (-1 / 2))]

def value1467 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (1 / 32)), (5, (-5 / 72)), (6, (-1 / 72)), (7, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (199, (1 / 6))]

def value1468 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 96)), (2, (-11 / 288)), (3, (-2 / 9)), (5, (5 / 72)), (7, (-1 / 6)), (8, (-1 / 9)), (35, (-1 / 6)), (51, (1 / 6)), (52, (-1 / 18)), (59, (1 / 6))]

def value1469 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (-5 / 144)), (5, (1 / 72)), (6, (-5 / 288)), (8, (-1 / 9)), (56, (1 / 6)), (201, (1 / 6))]

def value1470 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-1 / 16)), (2, (-19 / 288)), (5, (1 / 9)), (7, (-1 / 9)), (8, (-1 / 6)), (51, (1 / 6)), (52, (-1 / 18)), (59, (1 / 6))]

def value1471 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (35, (-1 / 18)), (51, (1 / 6)), (54, (1 / 6)), (59, (1 / 6)), (74, (-1 / 2)), (199, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1472 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 96)), (2, (-1 / 36)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 9)), (13, (-1 / 18)), (51, (1 / 6)), (56, (1 / 6)), (59, (1 / 6)), (76, (-1 / 2)), (201, (1 / 6))]

def value1473 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (7, (-1 / 18)), (23, (1 / 6)), (54, (1 / 6)), (72, (-1 / 2)), (282, (-1 / 2)), (287, (-1 / 2))]

def value1474 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (51, (1 / 6)), (54, (1 / 6)), (74, (-1 / 2)), (282, (-1 / 2)), (289, (-1 / 2))]

def value1475 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 18)), (8, (-1 / 9)), (10, (1 / 6)), (35, (-1 / 9)), (72, (-1 / 2))]

def value1476 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 6)), (8, (-1 / 18)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 18)), (59, (1 / 6)), (73, (-1 / 2))]

def value1477 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (5 / 72)), (7, (-5 / 18)), (8, (-1 / 18)), (10, (1 / 6)), (35, (-1 / 9)), (74, (-1 / 2))]

def value1478 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-5 / 144)), (3, (-1 / 6)), (5, (1 / 18)), (7, (-1 / 9)), (8, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (59, (1 / 6)), (75, (-1 / 2))]

def value1479 : Sparse (Fin 909) := [(3, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 3)), (59, (1 / 3)), (72, (-1 / 2)), (199, (1 / 6))]

def value1480 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-2 / 9)), (10, (1 / 6)), (12, (-1 / 6)), (13, (-2 / 9)), (59, (1 / 3)), (74, (-1 / 2)), (201, (1 / 6))]

def value1481 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (51, (1 / 6)), (56, (1 / 6)), (76, (-1 / 2)), (286, (-1 / 2)), (288, (-1 / 2))]

def value1482 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (59, (1 / 6)), (201, (1 / 3)), (287, (-1 / 2)), (726, (1 / 6))]

def value1483 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-1 / 32)), (5, (1 / 72)), (6, (-1 / 72)), (13, (-1 / 18)), (52, (-1 / 9)), (82, (-1 / 18)), (128, (-1 / 6)), (199, (1 / 6)), (201, (1 / 3)), (267, (1 / 3))]

def value1484 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 24)), (2, (-1 / 24)), (5, (1 / 36)), (6, (-1 / 144)), (8, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 9)), (52, (-1 / 9)), (59, (1 / 3)), (199, (1 / 6))]

def value1485 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 144)), (2, (-5 / 144)), (5, (1 / 12)), (7, (-1 / 9)), (8, (1 / 6)), (74, (-1 / 2))]

def value1486 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 18)), (8, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (59, (1 / 3)), (201, (1 / 6))]

def value1487 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 288)), (2, (-1 / 24)), (5, (7 / 72)), (7, (-1 / 18)), (8, (-1 / 9)), (76, (-1 / 2))]

def value1488 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (1 / 288)), (3, (-1 / 9)), (5, (-1 / 72)), (7, (-1 / 18)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6)), (228, (1 / 6)), (277, (1 / 6)), (290, (-1 / 2))]

def value1489 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 18)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (228, (1 / 3)), (277, (1 / 6)), (291, (-1 / 2))]

def value1490 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (55, (1 / 6)), (77, (-1 / 2)), (290, (-1 / 2)), (291, (-1 / 2))]

def value1491 : Sparse (Fin 909) := [(1, (7 / 288)), (2, (-5 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (35, (-1 / 9)), (54, (1 / 6)), (69, (-1 / 18)), (70, (-1 / 18)), (291, (-1 / 2))]

def value1492 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (-1 / 96)), (5, (-1 / 18)), (6, (-1 / 288)), (27, (-1 / 24)), (55, (1 / 6)), (228, (1 / 6))]

def value1493 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (1 / 288)), (5, (-1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (27, (-1 / 12)), (51, (1 / 6))]

def value1494 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 288)), (5, (-1 / 72)), (6, (-1 / 144)), (7, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (199, (1 / 6)), (228, (1 / 3)), (271, (1 / 3))]

def value1495 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 36)), (2, (1 / 36)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 3)), (228, (1 / 6))]

def value1496 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 18)), (51, (1 / 6)), (77, (-1 / 2))]

def value1497 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 72)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 96)), (35, (-1 / 9)), (52, (-1 / 9)), (56, (1 / 6)), (201, (1 / 6)), (228, (1 / 3)), (275, (1 / 3))]

def value1498 : Sparse (Fin 909) := [(0, (1 / 720)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (8, (-1 / 9)), (26, (-1 / 18)), (56, (1 / 3)), (228, (1 / 6))]

def value1499 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 144)), (2, (-1 / 24)), (3, (-5 / 18)), (5, (1 / 24)), (7, (-2 / 9)), (8, (-1 / 18)), (12, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 3)), (54, (1 / 6))]

def value1500 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 32)), (2, (-17 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-2 / 9)), (51, (1 / 3)), (56, (1 / 6))]

def value1501 : Sparse (Fin 909) := [(0, (1 / 720)), (2, (-1 / 144)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (26, (-1 / 18)), (54, (1 / 6)), (55, (1 / 6)), (77, (-1 / 2)), (228, (1 / 6))]

def value1502 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (8, (-1 / 18)), (24, (1 / 6)), (26, (-1 / 18)), (55, (1 / 6)), (56, (1 / 6)), (78, (-1 / 2)), (228, (1 / 6))]

def value1503 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-13 / 288)), (2, (1 / 96)), (3, (-1 / 9)), (5, (1 / 24)), (7, (-1 / 9)), (23, (1 / 6)), (27, (-1 / 24)), (54, (1 / 6))]

def value1504 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (-11 / 288)), (3, (-2 / 9)), (5, (1 / 36)), (7, (-1 / 6)), (24, (1 / 6)), (27, (-1 / 24)), (51, (1 / 6))]

def value1505 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 72)), (5, (1 / 24)), (8, (-1 / 9)), (24, (1 / 6)), (27, (-1 / 24)), (56, (1 / 6))]

def value1506 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 96)), (2, (-5 / 96)), (5, (1 / 36)), (8, (-1 / 6)), (27, (-1 / 24)), (30, (1 / 6)), (51, (1 / 6))]

def value1507 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (27, (-1 / 24)), (51, (1 / 3)), (54, (1 / 3))]

def value1508 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (-1 / 36)), (3, (-1 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (8, (-1 / 18)), (24, (1 / 6)), (27, (-1 / 24)), (51, (1 / 3)), (56, (1 / 3))]

def value1509 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (51, (1 / 3)), (94, (-1 / 2)), (127, (1 / 6))]

def value1510 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (-1 / 288)), (3, (-2 / 9)), (4, (-1 / 6)), (12, (-1 / 18)), (26, (-1 / 9)), (51, (1 / 6)), (54, (1 / 6)), (56, (1 / 6)), (78, (-1 / 2)), (228, (1 / 6))]

def value1511 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (26, (-1 / 9)), (51, (1 / 6)), (56, (1 / 3)), (77, (-1 / 2)), (228, (1 / 6))]

def value1512 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 9)), (12, (-1 / 18)), (51, (1 / 3)), (54, (1 / 6))]

def value1513 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-7 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (51, (1 / 3)), (56, (1 / 6))]

def value1514 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-2 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 9)), (23, (1 / 6)), (55, (1 / 3)), (79, (-1 / 2))]

def value1515 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (33, (1 / 6)), (122, (-1 / 2)), (299, (-1 / 2)), (300, (-1 / 2))]

def value1516 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-2 / 9)), (4, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 6)), (13, (-1 / 9)), (24, (1 / 6)), (55, (1 / 3)), (80, (-1 / 2))]

def value1517 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 72)), (3, (-2 / 9)), (7, (-1 / 18)), (23, (1 / 3)), (24, (1 / 3)), (79, (-1 / 2))]

def value1518 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 3)), (24, (1 / 6)), (27, (-1 / 12)), (55, (1 / 6))]

def value1519 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 144)), (2, (-5 / 288)), (3, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (27, (-1 / 24)), (51, (1 / 6)), (55, (1 / 6)), (122, (-1 / 2))]

def value1520 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (5 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18)), (24, (1 / 3)), (27, (-1 / 12)), (30, (1 / 6)), (55, (1 / 6))]

def value1521 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 144)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (23, (1 / 6)), (24, (1 / 3)), (27, (-1 / 8))]

def value1522 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 6)), (12, (-1 / 9)), (23, (1 / 3)), (26, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 6)), (54, (1 / 6)), (55, (1 / 3)), (65, (1 / 6))]

def value1523 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (-1 / 96)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 3)), (27, (-1 / 24)), (55, (1 / 3))]

def value1524 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 24)), (2, (-1 / 36)), (23, (1 / 6)), (27, (-1 / 8)), (30, (1 / 3))]

def value1525 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (13 / 144)), (2, (-1 / 36)), (24, (1 / 3)), (27, (-1 / 8)), (30, (1 / 6))]

def value1526 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-5 / 48)), (3, (-2 / 3)), (5, (1 / 3)), (6, (-1 / 96)), (7, (-1 / 1)), (8, (-1 / 3)), (26, (-1 / 6)), (35, (-4 / 3)), (52, (-1 / 6)), (67, (-1 / 3)), (69, (-2 / 3)), (70, (-2 / 3)), (71, (-1 / 6)), (257, (-1 / 6))]

def value1527 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (2, (-5 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 96)), (7, (-2 / 3)), (8, (-1 / 6)), (26, (-1 / 2)), (35, (-1 / 1)), (52, (-1 / 3)), (67, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 6)), (81, (1 / 2)), (256, (1 / 2)), (257, (-1 / 6)), (495, (-1 / 6))]

def value1528 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-7 / 96)), (2, (-13 / 96)), (3, (-1 / 3)), (5, (1 / 3)), (6, (-1 / 96)), (7, (-2 / 3)), (8, (-1 / 2)), (35, (-1 / 3)), (52, (-1 / 6)), (69, (-1 / 2)), (70, (-1 / 6)), (71, (-2 / 3)), (81, (1 / 2)), (256, (1 / 2))]

def value1529 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 32)), (2, (-1 / 24)), (3, (-2 / 3)), (5, (7 / 24)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-1 / 3)), (26, (-1 / 3)), (35, (-7 / 6)), (52, (-1 / 3)), (67, (-1 / 3))]

def value1530 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 32)), (2, (-1 / 8)), (3, (-4 / 3)), (4, (-1 / 3)), (5, (1 / 4)), (6, (-1 / 96)), (7, (-1 / 1)), (8, (-1 / 3)), (26, (-2 / 3)), (35, (-7 / 6)), (52, (-1 / 3)), (67, (-1 / 3)), (81, (1 / 1))]

def value1531 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-5 / 32)), (2, (-11 / 48)), (3, (-1 / 3)), (5, (11 / 24)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-1 / 2)), (35, (-1 / 3)), (52, (-1 / 3)), (81, (1 / 2))]

def value1532 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 12)), (2, (-1 / 32)), (3, (-5 / 3)), (4, (-1 / 2)), (5, (1 / 24)), (7, (-5 / 6)), (11, (-1 / 6)), (26, (-4 / 3)), (34, (-1 / 3)), (35, (-3 / 2)), (52, (-1 / 6)), (67, (-2 / 3)), (81, (1 / 1)), (228, (1 / 2)), (273, (1 / 2)), (276, (-1 / 6))]

def value1533 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-7 / 32)), (2, (-7 / 24)), (3, (-2 / 3)), (5, (11 / 24)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-1 / 2)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-5 / 6)), (52, (-2 / 3)), (67, (-1 / 6)), (81, (1 / 1)), (306, (1 / 2)), (307, (1 / 2))]

def value1534 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 96)), (2, (-1 / 8)), (3, (-1 / 2)), (5, (5 / 24)), (6, (-1 / 32)), (7, (-2 / 3)), (8, (-1 / 3)), (10, (1 / 2)), (35, (-1 / 2)), (52, (-1 / 3)), (55, (1 / 2)), (81, (1 / 1)), (228, (1 / 1)), (273, (1 / 1)), (306, (1 / 2))]

def value1535 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (3 / 32)), (3, (-1 / 2)), (5, (1 / 4)), (6, (-1 / 48)), (7, (-2 / 3)), (8, (-1 / 6)), (11, (-1 / 3)), (13, (-1 / 6)), (26, (-1 / 1)), (34, (-1 / 3)), (35, (-11 / 6)), (67, (-5 / 6)), (82, (-1 / 6)), (276, (-1 / 3)), (307, (1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2560 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (11 / 288)), (2, (-11 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (35, (-1 / 18))]

def value2561 : Sparse (Fin 909) := [(1, (-13 / 288)), (2, (-13 / 288)), (3, (-1 / 9)), (5, (7 / 72)), (7, (-1 / 18)), (8, (-1 / 9)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 6)), (59, (2 / 3)), (201, (1 / 6))]

def value2562 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (1 / 288)), (3, (-1 / 6)), (13, (-1 / 18)), (26, (-1 / 6)), (34, (-1 / 18)), (35, (-1 / 18)), (204, (-1 / 2)), (238, (1 / 6)), (398, (-1 / 2))]

def value2563 : Sparse (Fin 909) := [(1, (-11 / 288)), (2, (1 / 48)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 96)), (13, (-5 / 18)), (35, (-2 / 9)), (52, (-2 / 9)), (60, (-2 / 9)), (128, (-1 / 18))]

def value2564 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (7 / 72)), (6, (-1 / 72)), (7, (-2 / 9)), (8, (-1 / 6)), (13, (-1 / 18)), (35, (-2 / 9)), (71, (-1 / 18)), (82, (-1 / 18)), (309, (1 / 6))]

def value2565 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 9)), (13, (-1 / 18)), (52, (-1 / 18)), (71, (-1 / 18)), (309, (1 / 6)), (739, (-1 / 2))]

def value2566 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (5 / 72)), (6, (-1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 9)), (739, (-1 / 2))]

def value2567 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (506, (-1 / 2))]

def value2568 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-11 / 288)), (3, (-2 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (13, (-1 / 18)), (35, (-1 / 6)), (52, (-5 / 18)), (201, (1 / 6)), (327, (-1 / 2))]

def value2569 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 32)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 24)), (8, (-1 / 18)), (13, (-1 / 18)), (52, (-1 / 18)), (102, (-1 / 2)), (327, (-1 / 2))]

def value2570 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 96)), (2, (-5 / 96)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 288)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-2 / 9)), (86, (-1 / 2)), (328, (-1 / 2))]

def value2571 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 36)), (2, (-1 / 18)), (3, (-1 / 9)), (5, (1 / 36)), (8, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 9)), (102, (-1 / 2))]

def value2572 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (1 / 24)), (35, (-1 / 18)), (52, (-2 / 9)), (102, (-1 / 2)), (103, (-1 / 2))]

def value2573 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-5 / 144)), (3, (-2 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 18)), (35, (-5 / 18)), (52, (-1 / 3)), (328, (-1 / 2))]

def value2574 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (69, (-1 / 18)), (71, (-1 / 18)), (124, (1 / 6)), (236, (1 / 6))]

def value2575 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-1 / 36)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (7, (-1 / 9)), (8, (-1 / 6)), (13, (-1 / 18)), (35, (-1 / 18)), (59, (1 / 6)), (201, (1 / 6))]

def value2576 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 288)), (2, (-5 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 6)), (51, (1 / 6))]

def value2577 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 36)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 9)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (59, (1 / 6))]

def value2578 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 96)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-1 / 18))]

def value2579 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (13 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 18))]

def value2580 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (7 / 288)), (2, (1 / 72)), (3, (-1 / 9)), (26, (-1 / 18))]

def value2581 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (1 / 18)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 9))]

def value2582 : Sparse (Fin 909) := [(0, (-1 / 72)), (1, (7 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 9))]

def value2583 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 16)), (2, (-1 / 144)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 6))]

def value2584 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (1 / 36)), (2, (-1 / 96)), (3, (-1 / 18))]

def value2585 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 96)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (26, (-1 / 18)), (31, (1 / 6))]

def value2586 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-13 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (12, (-1 / 18))]

def value2587 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 144)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-2 / 9)), (12, (-1 / 18))]

def value2588 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (23 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18))]

def value2589 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 96)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 36)), (8, (-1 / 18)), (51, (1 / 6))]

def value2590 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 96)), (3, (-1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6))]

def value2591 : Sparse (Fin 909) := [(0, (1 / 720)), (2, (1 / 72)), (3, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 144)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (54, (1 / 6)), (228, (1 / 6))]

def value2592 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 72)), (6, (-1 / 72)), (8, (-1 / 18))]

def value2593 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2594 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (-1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18))]

def value2595 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 72)), (2, (-1 / 32)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18))]

def value2596 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 18)), (2, (-7 / 144)), (5, (5 / 72)), (6, (-1 / 288)), (8, (-2 / 9))]

def value2597 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 9))]

def value2598 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 9))]

def value2599 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (1 / 288)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 144)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2600 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (11 / 288)), (2, (1 / 96)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 6))]

def value2601 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 96)), (2, (-1 / 72)), (3, (-2 / 9)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2602 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-13 / 288)), (3, (-2 / 9)), (5, (1 / 18)), (6, (-1 / 96)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 6))]

def value2603 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (2, (-1 / 24)), (5, (1 / 12)), (6, (-1 / 72)), (52, (-1 / 9))]

def value2604 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (-11 / 288)), (3, (-2 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 9))]

def value2605 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (-1 / 72))]

def value2606 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 16)), (2, (-11 / 144)), (3, (-1 / 9)), (5, (5 / 36)), (6, (-5 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 9)), (52, (-2 / 9))]

def value2607 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (5 / 72)), (12, (-1 / 18))]

def value2608 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 16)), (2, (-13 / 288)), (3, (-1 / 3)), (4, (-1 / 18)), (12, (-1 / 6)), (13, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 18))]

def value2609 : Sparse (Fin 909) := [(0, (-1 / 48)), (1, (11 / 144)), (3, (-1 / 9)), (4, (-1 / 9))]

def value2610 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-7 / 144)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6))]

def value2611 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (7 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 18))]

def value2612 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 8)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (12, (-1 / 18))]

def value2613 : Sparse (Fin 909) := [(0, (-3 / 160)), (1, (1 / 144)), (2, (-1 / 288)), (3, (-1 / 18))]

def value2614 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (7 / 144)), (2, (-1 / 36)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 9))]

def value2615 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 36)), (2, (-1 / 96)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6))]

def value2616 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 36)), (2, (1 / 36)), (5, (1 / 72)), (52, (-1 / 18))]

def value2617 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (5 / 288)), (2, (1 / 288)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-5 / 18))]

def value2618 : Sparse (Fin 909) := [(0, (7 / 240)), (1, (5 / 144)), (2, (-1 / 72)), (28, (-1 / 2)), (30, (1 / 6))]

def value2619 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18))]

def value2620 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18))]

def value2621 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (1 / 36)), (8, (-1 / 18)), (52, (-1 / 18))]

def value2622 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (81, (1 / 6))]

def value2623 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 18)), (2, (-1 / 72)), (3, (-1 / 9)), (4, (-1 / 18)), (31, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2816 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (5 / 288)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 18)), (54, (1 / 6)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2817 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18))]

def value2818 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-5 / 288)), (5, (1 / 18)), (6, (-1 / 288)), (8, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2819 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 18)), (2, (-1 / 144)), (5, (1 / 72)), (7, (-1 / 18))]

def value2820 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-1 / 96)), (5, (-1 / 72)), (6, (-1 / 288)), (8, (-1 / 9)), (9, (1 / 72)), (69, (-1 / 18))]

def value2821 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 32)), (2, (1 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18))]

def value2822 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (1 / 72)), (2, (-1 / 48)), (5, (1 / 72)), (8, (-1 / 18))]

def value2823 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 144)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 9))]

def value2824 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 72)), (3, (-2 / 9)), (7, (-1 / 18)), (12, (-1 / 6)), (23, (1 / 6)), (25, (1 / 6))]

def value2825 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2826 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-5 / 96)), (3, (-2 / 9)), (5, (1 / 24)), (7, (-1 / 18)), (13, (-1 / 6)), (34, (-1 / 18)), (52, (-1 / 6)), (64, (1 / 6)), (69, (-1 / 18)), (125, (1 / 6))]

def value2827 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (69, (-1 / 18)), (125, (1 / 6))]

def value2828 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (25 / 288)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 18)), (24, (1 / 6))]

def value2829 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-1 / 32)), (3, (-5 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 9)), (69, (-1 / 18)), (70, (-1 / 18))]

def value2830 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 36)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18))]

def value2831 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (1 / 18)), (2, (-11 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18))]

def value2832 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 9)), (6, (-1 / 96)), (7, (-1 / 9)), (8, (-1 / 9)), (9, (1 / 72)), (35, (-1 / 18)), (52, (-1 / 9)), (69, (-1 / 9)), (70, (-1 / 18)), (71, (-1 / 9))]

def value2833 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (5 / 72)), (2, (1 / 24)), (5, (1 / 72)), (6, (-1 / 288)), (31, (1 / 6)), (123, (1 / 6)), (237, (1 / 6)), (239, (-1 / 2))]

def value2834 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 36)), (5, (1 / 36)), (6, (-1 / 144)), (87, (-1 / 2)), (237, (1 / 6))]

def value2835 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 36)), (5, (1 / 36)), (6, (-1 / 144)), (25, (1 / 6)), (123, (1 / 3)), (226, (1 / 6))]

def value2836 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 18)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9))]

def value2837 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (-7 / 288)), (2, (1 / 96)), (5, (1 / 72)), (6, (-1 / 288)), (27, (-1 / 24)), (30, (1 / 6)), (236, (1 / 6)), (253, (-1 / 2))]

def value2838 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 144)), (2, (-1 / 144)), (28, (-1 / 2)), (30, (1 / 6)), (253, (-1 / 1))]

def value2839 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-19 / 288)), (2, (1 / 144)), (5, (1 / 72)), (27, (-1 / 24)), (203, (-1 / 2)), (253, (-1 / 2))]

def value2840 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 36)), (5, (1 / 36)), (6, (-1 / 144)), (216, (-1 / 2)), (236, (1 / 6))]

def value2841 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 96)), (8, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 6))]

def value2842 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-1 / 144)), (5, (1 / 72)), (6, (-1 / 288))]

def value2843 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 144)), (2, (-5 / 96)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9))]

def value2844 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (7 / 96)), (2, (-1 / 288)), (3, (-1 / 3)), (4, (-2 / 9)), (26, (-2 / 9)), (35, (-1 / 18)), (55, (1 / 6))]

def value2845 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-5 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (5 / 72)), (6, (-1 / 72)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-2 / 9)), (52, (-1 / 6)), (228, (1 / 6))]

def value2846 : Sparse (Fin 909) := [(0, (-11 / 720)), (1, (1 / 72)), (2, (-1 / 144))]

def value2847 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (11 / 288)), (2, (1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-2 / 9)), (26, (-1 / 18)), (35, (-1 / 18)), (56, (1 / 6))]

def value2848 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 6)), (5, (1 / 72)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-5 / 18)), (35, (-1 / 18)), (52, (-1 / 18))]

def value2849 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 3))]

def value2850 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-5 / 144)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18))]

def value2851 : Sparse (Fin 909) := [(0, (-7 / 360)), (1, (1 / 12)), (2, (-1 / 72))]

def value2852 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (54, (1 / 6)), (69, (-1 / 18)), (125, (1 / 6))]

def value2853 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 18)), (9, (1 / 72)), (35, (-1 / 9)), (52, (-2 / 9)), (69, (-1 / 18))]

def value2854 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-5 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (8, (-1 / 18)), (9, (1 / 72)), (52, (-1 / 18)), (71, (-1 / 18))]

def value2855 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 6)), (51, (1 / 6)), (69, (-1 / 18)), (71, (-1 / 18))]

def value2856 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 144)), (2, (-1 / 36)), (8, (-1 / 18)), (30, (1 / 6))]

def value2857 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 144)), (2, (-1 / 36)), (5, (1 / 72)), (8, (-1 / 18))]

def value2858 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (-5 / 96)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (71, (-1 / 18)), (126, (1 / 6))]

def value2859 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 72)), (2, (-1 / 36)), (5, (1 / 18)), (6, (-1 / 288)), (8, (-1 / 18)), (71, (-1 / 9))]

def value2860 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 9)), (2, (-1 / 144)), (3, (-1 / 3)), (5, (1 / 72)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 9)), (35, (-1 / 9))]

def value2861 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 16)), (2, (1 / 36)), (3, (-2 / 9)), (12, (-2 / 9)), (13, (-1 / 3)), (35, (-1 / 9)), (54, (1 / 3))]

def value2862 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-5 / 144)), (3, (-1 / 6)), (5, (7 / 72)), (6, (-1 / 96)), (7, (-1 / 3)), (9, (1 / 72)), (35, (-1 / 9)), (69, (-1 / 6)), (70, (-1 / 9))]

def value2863 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 288)), (2, (1 / 32)), (3, (1 / 9)), (5, (-5 / 24)), (6, (7 / 288)), (7, (1 / 2)), (8, (1 / 9)), (9, (-1 / 9)), (35, (1 / 6)), (69, (10 / 9)), (70, (2 / 3)), (71, (4 / 9)), (256, (-1 / 3)), (277, (-1 / 6)), (279, (1 / 2)), (726, (-1 / 6))]

def value2864 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 12)), (2, (1 / 8)), (3, (1 / 18)), (5, (-11 / 36)), (6, (1 / 36)), (7, (5 / 18)), (8, (5 / 9)), (9, (-1 / 9)), (35, (1 / 18)), (69, (1 / 2)), (70, (1 / 18)), (71, (5 / 3)), (256, (-1 / 3)), (277, (-1 / 6)), (280, (1 / 2)), (818, (-1 / 6))]

def value2865 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 96)), (2, (11 / 144)), (3, (4 / 9)), (5, (-7 / 36)), (6, (1 / 144)), (7, (7 / 9)), (8, (2 / 9)), (9, (-1 / 36)), (35, (5 / 9)), (52, (2 / 9)), (69, (1 / 2)), (70, (5 / 18)), (71, (2 / 9)), (256, (-2 / 3)), (277, (-1 / 6)), (279, (1 / 2)), (280, (1 / 1)), (726, (-1 / 2))]

def value2866 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 72)), (2, (23 / 144)), (3, (1 / 9)), (5, (-3 / 8)), (6, (7 / 288)), (7, (7 / 18)), (8, (13 / 18)), (9, (-1 / 12)), (35, (1 / 9)), (52, (1 / 9)), (69, (5 / 9)), (70, (1 / 9)), (71, (13 / 9)), (256, (-1 / 3)), (280, (1 / 2)), (281, (1 / 2)), (726, (-1 / 6)), (818, (-1 / 6))]

def value2867 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (43 / 288)), (2, (55 / 288)), (5, (-17 / 36)), (6, (1 / 36)), (7, (4 / 9)), (8, (8 / 9)), (9, (-1 / 12)), (52, (1 / 9)), (69, (13 / 18)), (70, (5 / 18)), (71, (10 / 9)), (256, (-1 / 3)), (281, (1 / 1)), (818, (-1 / 3))]

def value2868 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (5 / 48)), (3, (7 / 18)), (5, (-17 / 72)), (6, (5 / 288)), (7, (5 / 9)), (8, (2 / 9)), (9, (-1 / 18)), (35, (4 / 9)), (52, (1 / 3)), (69, (4 / 9)), (70, (2 / 9)), (71, (4 / 9)), (256, (-1 / 1)), (277, (-1 / 2)), (279, (1 / 2)), (280, (1 / 1)), (726, (-1 / 6)), (818, (-1 / 3))]

def value2869 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 288)), (2, (13 / 288)), (3, (1 / 18)), (5, (-1 / 9)), (6, (1 / 96)), (7, (2 / 9)), (8, (1 / 9)), (9, (-1 / 9)), (10, (-1 / 6)), (27, (1 / 24)), (35, (1 / 18)), (55, (-1 / 6)), (69, (1 / 6)), (70, (1 / 18)), (71, (1 / 9)), (228, (-1 / 3)), (277, (-1 / 6)), (282, (1 / 2)), (726, (-1 / 6))]

def value2870 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (3, (1 / 3)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 18)), (23, (-1 / 3)), (26, (1 / 9)), (35, (1 / 6)), (54, (-1 / 2)), (55, (-1 / 6)), (72, (1 / 2)), (77, (1 / 1)), (199, (-1 / 6)), (228, (-1 / 3)), (282, (1 / 2)), (286, (1 / 1)), (287, (1 / 1)), (726, (-1 / 6))]

def value2871 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 288)), (2, (5 / 144)), (3, (5 / 18)), (4, (1 / 6)), (5, (-1 / 24)), (6, (1 / 144)), (7, (1 / 9)), (8, (-1 / 18)), (12, (1 / 18)), (24, (-1 / 6)), (26, (1 / 9)), (35, (1 / 18)), (51, (-1 / 6)), (52, (1 / 18)), (54, (-1 / 6)), (55, (-1 / 6)), (56, (-1 / 3)), (74, (1 / 2)), (78, (1 / 1)), (201, (-1 / 6)), (228, (-1 / 3)), (282, (1 / 2)), (288, (1 / 1)), (289, (1 / 1)), (726, (-1 / 6))]

def value2872 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (-1 / 18)), (3, (1 / 3)), (6, (1 / 48)), (8, (2 / 9)), (10, (-1 / 6)), (23, (-1 / 6)), (27, (1 / 24)), (35, (1 / 3)), (54, (-1 / 3)), (72, (1 / 2)), (199, (-1 / 6))]

def value2873 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 36)), (2, (7 / 72)), (3, (13 / 18)), (5, (-5 / 36)), (6, (1 / 288)), (7, (1 / 2)), (8, (1 / 3)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (24, (-1 / 6)), (27, (1 / 24)), (35, (1 / 2)), (51, (-1 / 3)), (52, (1 / 9)), (59, (-1 / 3)), (73, (1 / 2))]

def value2874 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (13 / 144)), (3, (1 / 9)), (5, (-1 / 8)), (6, (7 / 288)), (7, (7 / 18)), (8, (1 / 18)), (10, (-1 / 6)), (24, (-1 / 6)), (27, (1 / 24)), (35, (1 / 9)), (56, (-1 / 3)), (74, (1 / 2)), (201, (-1 / 6))]

def value2875 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 72)), (2, (29 / 144)), (3, (1 / 6)), (5, (-1 / 4)), (6, (1 / 288)), (7, (7 / 18)), (8, (4 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (27, (1 / 24)), (30, (-1 / 6)), (35, (1 / 18)), (51, (-1 / 3)), (52, (1 / 9)), (59, (-1 / 3)), (75, (1 / 2))]

def value2876 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-5 / 144)), (2, (11 / 144)), (3, (2 / 3)), (5, (-7 / 72)), (7, (7 / 18)), (8, (2 / 9)), (10, (-1 / 6)), (12, (7 / 18)), (13, (5 / 9)), (23, (-1 / 6)), (27, (1 / 24)), (35, (2 / 9)), (51, (-2 / 3)), (54, (-2 / 3)), (59, (-2 / 3)), (72, (1 / 2)), (74, (1 / 1)), (199, (-1 / 2))]

def value2877 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 36)), (2, (1 / 16)), (3, (7 / 18)), (4, (1 / 6)), (5, (-5 / 72)), (6, (1 / 288)), (8, (2 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (51, (-1 / 2)), (52, (1 / 9)), (56, (-2 / 3)), (59, (-1 / 6)), (76, (1 / 1)), (77, (1 / 2)), (201, (-1 / 3)), (228, (-1 / 6)), (286, (1 / 1)), (287, (1 / 2)), (288, (1 / 1)), (726, (-1 / 6))]

def value2878 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 32)), (2, (5 / 36)), (3, (1 / 6)), (5, (-17 / 72)), (6, (1 / 72)), (7, (4 / 9)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (54, (-1 / 6)), (59, (-1 / 3)), (74, (1 / 2)), (199, (-1 / 6))]

def value2879 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (13 / 144)), (2, (47 / 288)), (3, (1 / 3)), (4, (1 / 18)), (5, (-7 / 24)), (6, (5 / 288)), (7, (1 / 3)), (8, (1 / 2)), (13, (1 / 18)), (35, (1 / 6)), (51, (-1 / 3)), (52, (1 / 9)), (56, (-1 / 6)), (59, (-1 / 3)), (76, (1 / 2)), (201, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1536 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 32)), (2, (1 / 16)), (3, (-1 / 2)), (5, (-1 / 12)), (9, (1 / 24)), (35, (-1 / 3)), (69, (-1 / 2)), (70, (-1 / 3))]

def value1537 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-5 / 96)), (2, (-3 / 32)), (3, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 24)), (7, (-1 / 6)), (8, (-1 / 3)), (9, (1 / 6)), (52, (-1 / 3)), (58, (-1 / 96)), (69, (-1 / 6)), (71, (-1 / 3)), (308, (1 / 2)), (310, (-1 / 6))]

def value1538 : Sparse (Fin 909) := [(1, (-5 / 96)), (2, (-5 / 32)), (5, (1 / 4)), (6, (-1 / 48)), (7, (-1 / 3)), (8, (-1 / 3)), (9, (1 / 24)), (69, (-1 / 6)), (71, (-2 / 3))]

def value1539 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (-1 / 8)), (3, (-1 / 3)), (5, (5 / 12)), (6, (-1 / 24)), (7, (-2 / 3)), (8, (-2 / 3)), (9, (1 / 24)), (35, (-1 / 3)), (69, (-1 / 3)), (70, (-1 / 6)), (71, (-1 / 3))]

def value1540 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 16)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (7 / 24)), (6, (-1 / 32)), (7, (-1 / 3)), (8, (-1 / 6)), (9, (1 / 8)), (13, (-1 / 3)), (35, (-1 / 2)), (52, (-1 / 6)), (58, (-1 / 96)), (70, (-1 / 3)), (71, (-1 / 6)), (82, (-1 / 3)), (278, (-1 / 6)), (309, (1 / 2)), (310, (-1 / 6))]

def value1541 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-5 / 32)), (2, (-1 / 4)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (3 / 8)), (6, (-1 / 32)), (7, (-1 / 2)), (8, (-2 / 3)), (51, (3 / 2)), (52, (-1 / 2)), (308, (3 / 2)), (309, (1 / 1)), (310, (-1 / 6))]

def value1542 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-31 / 96)), (3, (-1 / 2)), (5, (13 / 24)), (6, (-1 / 32)), (7, (-1 / 1)), (8, (-1 / 1)), (35, (-1 / 3))]

def value1543 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-1 / 48)), (2, (-5 / 48)), (3, (-2 / 3)), (5, (3 / 8)), (6, (-1 / 48)), (7, (-1 / 1)), (8, (-2 / 3)), (10, (1 / 2)), (12, (-1 / 6)), (13, (-1 / 3)), (35, (-2 / 3)), (82, (-1 / 6))]

def value1544 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-5 / 18)), (8, (-1 / 18)), (35, (-1 / 18)), (69, (-2 / 9)), (70, (-1 / 18)), (71, (-1 / 6))]

def value1545 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (81, (1 / 6)), (256, (1 / 6)), (818, (1 / 6))]

def value1546 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 18)), (3, (-2 / 9)), (5, (1 / 12)), (6, (-1 / 144)), (7, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 3)), (256, (1 / 6)), (818, (1 / 6))]

def value1547 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-2 / 9)), (35, (-1 / 9)), (52, (-1 / 18)), (69, (-1 / 9)), (70, (-1 / 9)), (81, (1 / 6)), (256, (1 / 6)), (322, (-1 / 2))]

def value1548 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (1 / 96)), (3, (-1 / 6)), (5, (1 / 36)), (6, (-1 / 144)), (7, (-2 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (228, (1 / 6))]

def value1549 : Sparse (Fin 909) := [(2, (-1 / 288)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (83, (-1 / 2)), (228, (1 / 6))]

def value1550 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 9)), (84, (-1 / 2))]

def value1551 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (-1 / 32)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 48)), (35, (-1 / 18)), (52, (-1 / 6)), (228, (1 / 6))]

def value1552 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-5 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (26, (-1 / 18)), (52, (-1 / 18)), (81, (1 / 3)), (228, (1 / 6))]

def value1553 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 144)), (2, (-5 / 96)), (5, (1 / 12)), (6, (-1 / 288)), (8, (-1 / 18)), (52, (-1 / 18)), (85, (-1 / 2))]

def value1554 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 36)), (7, (1 / 9)), (8, (-1 / 9)), (35, (-1 / 9))]

def value1555 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 48)), (5, (-1 / 18)), (6, (-1 / 144)), (52, (-1 / 18)), (128, (-1 / 18)), (201, (1 / 6))]

def value1556 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-1 / 72)), (5, (1 / 24)), (7, (-1 / 9)), (8, (1 / 6)), (81, (1 / 6))]

def value1557 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 288)), (2, (-1 / 24)), (3, (-2 / 9)), (5, (1 / 18)), (7, (-5 / 18)), (8, (-1 / 18)), (35, (-5 / 18)), (52, (-1 / 6))]

def value1558 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 144)), (2, (-1 / 16)), (5, (1 / 8)), (6, (-1 / 32)), (8, (-1 / 18)), (52, (-1 / 18))]

def value1559 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-19 / 288)), (2, (-23 / 288)), (3, (-1 / 18)), (5, (1 / 9)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-2 / 9)), (52, (-1 / 9)), (81, (1 / 6))]

def value1560 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-13 / 288)), (2, (-19 / 288)), (3, (-1 / 18)), (5, (5 / 36)), (7, (-5 / 18)), (8, (-2 / 9)), (35, (-1 / 18))]

def value1561 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-7 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 18)), (81, (1 / 6)), (85, (-1 / 2)), (228, (1 / 6))]

def value1562 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-13 / 288)), (3, (-1 / 6)), (5, (7 / 72)), (7, (-2 / 9)), (8, (-2 / 9)), (35, (-1 / 6)), (81, (1 / 6))]

def value1563 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (5 / 72)), (6, (-5 / 288)), (7, (-1 / 18)), (35, (-2 / 9)), (52, (-5 / 18))]

def value1564 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (3, (-2 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-2 / 9)), (26, (-1 / 9)), (35, (-2 / 9)), (55, (1 / 6)), (67, (-1 / 18)), (228, (1 / 3)), (273, (1 / 6))]

def value1565 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (-1 / 288)), (3, (-5 / 18)), (7, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 6)), (26, (-1 / 18)), (34, (-1 / 18)), (35, (-1 / 9)), (55, (1 / 6)), (60, (-1 / 18)), (228, (1 / 6)), (273, (1 / 6)), (311, (-1 / 2))]

def value1566 : Sparse (Fin 909) := [(36, (-1 / 2)), (83, (-1 / 2)), (312, (-1 / 2)), (316, (-1 / 2))]

def value1567 : Sparse (Fin 909) := [(37, (-1 / 2)), (83, (-1 / 2)), (84, (-1 / 2)), (317, (-1 / 2))]

def value1568 : Sparse (Fin 909) := [(38, (-1 / 2)), (84, (-1 / 2)), (313, (-1 / 2)), (318, (-1 / 2))]

def value1569 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 9)), (5, (1 / 72)), (26, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (55, (1 / 6)), (67, (-1 / 18)), (81, (1 / 3)), (228, (1 / 3)), (273, (1 / 6))]

def value1570 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 9)), (33, (1 / 6)), (34, (-1 / 18)), (55, (1 / 6)), (81, (1 / 6)), (228, (1 / 6)), (273, (1 / 6)), (314, (-1 / 2)), (490, (1 / 6))]

def value1571 : Sparse (Fin 909) := [(39, (-1 / 2)), (85, (-1 / 2)), (315, (-1 / 2)), (319, (-1 / 2))]

def value1572 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 18)), (81, (1 / 6)), (84, (-1 / 2)), (311, (-1 / 2))]

def value1573 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 32)), (2, (-1 / 144)), (4, (-1 / 18)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 18)), (84, (-1 / 2)), (228, (1 / 6))]

def value1574 : Sparse (Fin 909) := [(3, (-1 / 6)), (10, (1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (33, (1 / 6)), (59, (1 / 6)), (311, (-1 / 2)), (313, (-1 / 2))]

def value1575 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 288)), (2, (-13 / 288)), (3, (-2 / 9)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (85, (-1 / 2)), (228, (1 / 6))]

def value1576 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 36)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18)), (81, (1 / 6)), (85, (-1 / 2)), (228, (1 / 6))]

def value1577 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (-1 / 72)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (33, (1 / 6)), (51, (1 / 3)), (59, (1 / 6)), (314, (-1 / 2)), (315, (-1 / 2))]

def value1578 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (33, (1 / 6)), (55, (1 / 6)), (312, (-1 / 2)), (314, (-1 / 2)), (330, (-1 / 2))]

def value1579 : Sparse (Fin 909) := [(3, (-1 / 18)), (4, (-1 / 18)), (26, (-1 / 18)), (81, (1 / 6)), (83, (-1 / 2)), (85, (-1 / 2)), (228, (1 / 6)), (314, (-1 / 2))]

def value1580 : Sparse (Fin 909) := [(3, (-2 / 9)), (4, (-1 / 18)), (26, (-2 / 9)), (81, (1 / 3)), (83, (-1 / 2)), (228, (1 / 3))]

def value1581 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (-1 / 72)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 9)), (81, (1 / 6)), (84, (-1 / 2)), (228, (1 / 6))]

def value1582 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 6)), (7, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 3)), (228, (1 / 3)), (321, (-1 / 2)), (492, (1 / 6))]

def value1583 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 9)), (73, (-1 / 2)), (201, (1 / 6))]

def value1584 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-1 / 36)), (3, (-1 / 18)), (5, (7 / 72)), (6, (-1 / 72)), (52, (-1 / 6)), (322, (-1 / 2)), (818, (1 / 6))]

def value1585 : Sparse (Fin 909) := [(0, (1 / 360)), (2, (-1 / 48)), (3, (-2 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (81, (1 / 3))]

def value1586 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 288)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (1 / 72)), (31, (1 / 6)), (33, (1 / 3)), (52, (-1 / 18)), (81, (1 / 3)), (311, (-1 / 2)), (490, (1 / 6))]

def value1587 : Sparse (Fin 909) := [(38, (-1 / 2)), (84, (-1 / 2)), (321, (-1 / 2)), (323, (-1 / 2))]

def value1588 : Sparse (Fin 909) := [(3, (-2 / 9)), (7, (-1 / 9)), (12, (-1 / 9)), (13, (-2 / 9)), (33, (1 / 6)), (35, (-2 / 9)), (60, (-1 / 9)), (81, (1 / 6)), (311, (-1 / 2)), (490, (1 / 6))]

def value1589 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 144)), (5, (-5 / 72)), (6, (-1 / 72)), (9, (1 / 72)), (54, (1 / 6)), (228, (1 / 3)), (492, (1 / 6))]

def value1590 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 48)), (2, (-5 / 144)), (3, (-1 / 3)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (75, (-1 / 2)), (201, (1 / 6))]

def value1591 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 36)), (2, (-17 / 288)), (3, (-1 / 18)), (5, (7 / 72)), (6, (-5 / 288)), (52, (-1 / 9)), (325, (-1 / 2)), (818, (1 / 6))]

def value1592 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 32)), (2, (-5 / 72)), (3, (-1 / 9)), (5, (1 / 24)), (8, (-1 / 18)), (52, (-1 / 9)), (81, (1 / 6)), (86, (-1 / 2))]

def value1593 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-11 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 9)), (33, (1 / 6)), (52, (-1 / 6)), (81, (1 / 6)), (128, (-1 / 18)), (326, (-1 / 2)), (490, (1 / 6))]

def value1594 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 32)), (2, (-11 / 288)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 6)), (51, (1 / 6)), (325, (-1 / 2)), (327, (-1 / 2))]

def value1595 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-11 / 288)), (2, (-5 / 72)), (3, (-1 / 9)), (5, (5 / 72)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 6)), (86, (-1 / 2))]

def value1596 : Sparse (Fin 909) := [(42, (-1 / 2)), (86, (-1 / 2)), (326, (-1 / 2)), (328, (-1 / 2))]

def value1597 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 24)), (3, (-1 / 6)), (5, (1 / 18)), (6, (-1 / 144)), (12, (-1 / 18)), (13, (-5 / 18)), (35, (-1 / 18)), (52, (-5 / 18)), (82, (-1 / 18)), (128, (-1 / 6)), (328, (-1 / 2))]

def value1598 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 18)), (52, (-1 / 6)), (54, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 9)), (228, (1 / 6)), (329, (-1 / 2)), (492, (1 / 6))]

def value1599 : Sparse (Fin 909) := [(39, (-1 / 2)), (85, (-1 / 2)), (329, (-1 / 2)), (330, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1600 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (33, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6)), (81, (1 / 6)), (228, (1 / 6)), (330, (-1 / 2)), (490, (1 / 6)), (492, (1 / 6))]

def value1601 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (7, (-1 / 9)), (11, (-1 / 18)), (26, (-2 / 9)), (33, (1 / 6)), (35, (-1 / 6)), (81, (1 / 3)), (228, (1 / 3)), (490, (1 / 6))]

def value1602 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 96)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (322, (-1 / 2)), (327, (-1 / 2))]

def value1603 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-7 / 144)), (3, (-2 / 9)), (5, (1 / 24)), (7, (-1 / 6)), (35, (-2 / 9)), (52, (-2 / 9)), (81, (1 / 6))]

def value1604 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 144)), (2, (-13 / 288)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (8, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (201, (1 / 6)), (327, (-1 / 2)), (818, (1 / 6))]

def value1605 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (2, (-5 / 144)), (3, (-1 / 6)), (5, (1 / 18)), (6, (-5 / 288)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-2 / 9)), (201, (1 / 6))]

def value1606 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (5 / 72)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 9)), (69, (-1 / 18)), (321, (-1 / 2))]

def value1607 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 3)), (59, (1 / 6)), (311, (-1 / 2)), (328, (-1 / 2))]

def value1608 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 3)), (59, (1 / 2)), (326, (-1 / 2))]

def value1609 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (59, (1 / 3)), (321, (-1 / 2)), (330, (-1 / 2))]

def value1610 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 18)), (55, (1 / 6)), (311, (-1 / 2)), (321, (-1 / 2)), (329, (-1 / 2))]

def value1611 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (84, (-1 / 2)), (85, (-1 / 2)), (228, (1 / 6)), (311, (-1 / 2))]

def value1612 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (7, (-1 / 9)), (24, (1 / 6)), (73, (-1 / 2)), (322, (-1 / 1))]

def value1613 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 18)), (35, (-2 / 9)), (73, (-1 / 2)), (81, (1 / 6))]

def value1614 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-5 / 144)), (5, (-1 / 72)), (6, (-1 / 144)), (9, (1 / 72)), (13, (-1 / 18)), (52, (-1 / 9)), (82, (-1 / 18)), (128, (-1 / 6)), (492, (1 / 6))]

def value1615 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (-5 / 96)), (5, (1 / 24)), (6, (-1 / 96)), (8, (-1 / 9)), (52, (-1 / 9)), (71, (-1 / 18)), (329, (-1 / 2))]

def value1616 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-13 / 288)), (2, (-1 / 24)), (3, (-1 / 9)), (5, (1 / 9)), (6, (-1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (35, (-1 / 6)), (52, (-2 / 9)), (328, (-1 / 2))]

def value1617 : Sparse (Fin 909) := [(1, (-7 / 288)), (2, (-1 / 36)), (5, (1 / 18)), (6, (-1 / 288)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (82, (-1 / 6)), (128, (-2 / 9)), (201, (1 / 6))]

def value1618 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 144)), (2, (-1 / 18)), (5, (1 / 9)), (7, (-1 / 9)), (8, (-1 / 6)), (75, (-1 / 2))]

def value1619 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (11 / 288)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 18)), (105, (-1 / 2)), (124, (1 / 6)), (236, (1 / 6)), (352, (-1 / 2))]

def value1620 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (23, (1 / 6)), (124, (1 / 2)), (196, (1 / 6)), (197, (1 / 6)), (236, (1 / 6)), (290, (-1 / 2))]

def value1621 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (125, (2 / 3)), (126, (1 / 3)), (352, (-1 / 2))]

def value1622 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 288)), (2, (-5 / 288)), (8, (-1 / 18)), (51, (1 / 6)), (102, (-1 / 2)), (327, (-1 / 2)), (352, (-1 / 2))]

def value1623 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-1 / 32)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 6)), (13, (-7 / 18)), (35, (-1 / 6)), (52, (-1 / 9)), (59, (1 / 6))]

def value1624 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (-7 / 144)), (3, (-1 / 6)), (5, (1 / 18)), (8, (-1 / 18)), (13, (-1 / 9)), (33, (1 / 6)), (52, (-1 / 9)), (59, (1 / 6))]

def value1625 : Sparse (Fin 909) := [(0, (1 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (8, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 6)), (52, (-1 / 18)), (59, (1 / 6)), (102, (-1 / 2))]

def value1626 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (1 / 96)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 9)), (52, (-1 / 18)), (59, (1 / 6)), (103, (-1 / 2))]

def value1627 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 96)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 18)), (7, (-2 / 9)), (8, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6))]

def value1628 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-11 / 288)), (3, (-2 / 9)), (5, (1 / 36)), (7, (-1 / 6)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-2 / 9)), (52, (-1 / 9)), (54, (1 / 6))]

def value1629 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6)), (87, (-1 / 2)), (228, (1 / 6))]

def value1630 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-17 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (26, (-1 / 18)), (27, (-1 / 24)), (55, (1 / 6))]

def value1631 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (11 / 288)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 72)), (12, (-1 / 6)), (13, (-1 / 9)), (27, (-1 / 24)), (51, (1 / 6)), (55, (1 / 6))]

def value1632 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (1 / 48)), (3, (-1 / 9)), (7, (-1 / 18)), (23, (1 / 6)), (25, (1 / 6)), (26, (-1 / 18)), (36, (-1 / 2)), (54, (1 / 3))]

def value1633 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 36)), (2, (-5 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 6)), (38, (-1 / 2)), (54, (1 / 6))]

def value1634 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 18)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 36)), (26, (-1 / 18)), (27, (-1 / 24)), (55, (1 / 6))]

def value1635 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (7 / 288)), (2, (-1 / 36)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (27, (-1 / 24)), (31, (1 / 6)), (33, (1 / 3)), (51, (1 / 6)), (55, (1 / 6))]

def value1636 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 288)), (2, (-1 / 72)), (3, (-1 / 9)), (4, (-1 / 18)), (8, (-1 / 18)), (13, (-1 / 18)), (24, (1 / 6)), (39, (-1 / 2)), (56, (1 / 6))]

def value1637 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (2, (1 / 24)), (3, (-1 / 18)), (5, (1 / 72)), (13, (-1 / 18)), (56, (1 / 6))]

def value1638 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 24)), (2, (-1 / 48)), (3, (-1 / 3)), (12, (-1 / 6)), (13, (-1 / 3)), (51, (1 / 6)), (54, (1 / 6))]

def value1639 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 48)), (2, (-1 / 32)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 9)), (33, (1 / 6)), (51, (1 / 6)), (56, (1 / 6))]

def value1640 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 48)), (2, (-1 / 16)), (3, (-2 / 9)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6))]

def value1641 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 144)), (2, (-1 / 96)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (42, (-1 / 2)), (51, (1 / 6)), (56, (1 / 6))]

def value1642 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (17 / 288)), (2, (1 / 96)), (3, (-1 / 9)), (12, (-1 / 9)), (33, (1 / 6)), (39, (-1 / 2)), (51, (1 / 6)), (54, (1 / 3))]

def value1643 : Sparse (Fin 909) := [(0, (1 / 360)), (2, (-1 / 24)), (3, (-1 / 3)), (4, (-1 / 18)), (7, (-1 / 18)), (26, (-1 / 6)), (33, (1 / 6)), (51, (1 / 6))]

def value1644 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (5 / 96)), (2, (19 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (12, (-1 / 18)), (13, (-2 / 9)), (54, (1 / 6))]

def value1645 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (25, (1 / 6)), (31, (1 / 6)), (39, (-1 / 2)), (87, (-1 / 2)), (100, (-1 / 2))]

def value1646 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (5 / 144)), (3, (-1 / 6)), (7, (-1 / 18)), (26, (-1 / 9)), (36, (-1 / 2)), (55, (1 / 6))]

def value1647 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (-1 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 18)), (26, (-1 / 18)), (37, (-1 / 2)), (55, (1 / 6))]

def value1648 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (26, (-1 / 9)), (39, (-1 / 2)), (55, (1 / 6))]

def value1649 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (5 / 144)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 18)), (33, (1 / 6)), (40, (-1 / 2)), (55, (1 / 6))]

def value1650 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-2 / 9)), (13, (-2 / 9)), (38, (-1 / 2)), (55, (1 / 6))]

def value1651 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (25, (1 / 6)), (39, (-1 / 2)), (51, (1 / 6)), (54, (1 / 6)), (89, (-1 / 2))]

def value1652 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 18)), (2, (-7 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 18)), (26, (-1 / 18)), (40, (-1 / 2)), (55, (1 / 6))]

def value1653 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (19 / 288)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-2 / 9)), (13, (-1 / 9)), (33, (1 / 6)), (39, (-1 / 2)), (55, (1 / 6))]

def value1654 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 9)), (33, (1 / 3)), (36, (-1 / 2)), (54, (1 / 6)), (55, (1 / 6))]

def value1655 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (3, (-5 / 18)), (4, (-1 / 18)), (26, (-1 / 6)), (33, (1 / 6)), (37, (-1 / 2)), (55, (1 / 6))]

def value1656 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (38, (-1 / 2)), (89, (-1 / 2)), (104, (-1 / 2))]

def value1657 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 72)), (2, (-1 / 36)), (4, (-1 / 9)), (26, (-1 / 9)), (38, (-1 / 2)), (55, (1 / 6))]

def value1658 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (52, (-1 / 18)), (95, (-1 / 2)), (322, (-1 / 2)), (379, (-1 / 2))]

def value1659 : Sparse (Fin 909) := [(23, (1 / 3)), (124, (1 / 3)), (196, (1 / 3)), (379, (-1 / 1))]

def value1660 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (97, (-1 / 2)), (124, (1 / 6)), (197, (1 / 6)), (378, (-1 / 2))]

def value1661 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (100, (-1 / 2)), (125, (1 / 6)), (126, (1 / 6)), (379, (-1 / 2))]

def value1662 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (55, (1 / 6)), (104, (-1 / 2)), (291, (-1 / 2)), (379, (-1 / 2))]

def value1663 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 9)), (7, (-1 / 18)), (51, (1 / 6)), (103, (-1 / 2)), (322, (-1 / 2)), (378, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1664 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (7, (-1 / 9)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 9)), (256, (1 / 6)), (378, (-1 / 2))]

def value1665 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (1 / 288)), (5, (1 / 72)), (31, (1 / 6)), (33, (1 / 6)), (52, (-1 / 18)), (81, (1 / 6))]

def value1666 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (1 / 288)), (3, (-5 / 18)), (7, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 9)), (81, (1 / 6)), (95, (-1 / 2))]

def value1667 : Sparse (Fin 909) := [(1, (1 / 144)), (5, (1 / 72)), (6, (-1 / 144)), (7, (-1 / 9)), (9, (1 / 72)), (35, (-1 / 9)), (52, (-1 / 9)), (54, (1 / 6)), (69, (-1 / 9)), (260, (1 / 3)), (492, (1 / 6))]

def value1668 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 6)), (52, (-1 / 9)), (98, (-1 / 2))]

def value1669 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-11 / 288)), (2, (-1 / 16)), (3, (-2 / 9)), (5, (1 / 36)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 18)), (52, (-1 / 6)), (102, (-1 / 2))]

def value1670 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 9)), (26, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 9)), (81, (1 / 6)), (104, (-1 / 2))]

def value1671 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 6)), (103, (-1 / 2))]

def value1672 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 96)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (25, (1 / 3)), (26, (-1 / 9)), (38, (-1 / 2)), (54, (1 / 6))]

def value1673 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (5 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (5, (1 / 72)), (31, (1 / 6)), (52, (-1 / 18)), (95, (-1 / 2))]

def value1674 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (5 / 144)), (2, (-1 / 48)), (3, (-2 / 9)), (12, (-1 / 9)), (13, (-1 / 9)), (31, (1 / 3)), (33, (1 / 3))]

def value1675 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (1 / 288)), (3, (-1 / 6)), (5, (1 / 18)), (7, (-2 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (54, (1 / 3)), (64, (1 / 6)), (69, (-1 / 18)), (260, (1 / 6))]

def value1676 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (1 / 288)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6)), (97, (-1 / 2))]

def value1677 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (1 / 18)), (43, (-1 / 2)), (97, (-1 / 2)), (98, (-1 / 2))]

def value1678 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 6)), (52, (-1 / 9)), (99, (-1 / 2))]

def value1679 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (44, (-1 / 2)), (99, (-1 / 2)), (100, (-1 / 2))]

def value1680 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 96)), (2, (13 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (25, (1 / 6)), (26, (-1 / 9)), (54, (1 / 6))]

def value1681 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (5 / 96)), (2, (-1 / 24)), (3, (-5 / 18)), (12, (-5 / 18)), (13, (-5 / 18))]

def value1682 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (5, (1 / 24)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-2 / 9))]

def value1683 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (-1 / 18)), (3, (-1 / 6)), (31, (1 / 6)), (33, (1 / 6))]

def value1684 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (11 / 288)), (2, (-1 / 72)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-2 / 9)), (13, (-2 / 9)), (33, (1 / 6)), (59, (1 / 6)), (101, (-1 / 2))]

def value1685 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (2, (-1 / 36)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (31, (1 / 6)), (33, (1 / 6)), (42, (-1 / 2))]

def value1686 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 72)), (2, (-1 / 24)), (3, (-1 / 3)), (4, (-1 / 9)), (12, (-1 / 9)), (13, (-2 / 9)), (42, (-1 / 2))]

def value1687 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (7 / 288)), (2, (-1 / 36)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 6)), (25, (1 / 6)), (26, (-1 / 18)), (39, (-1 / 2)), (54, (1 / 6))]

def value1688 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (31, (1 / 6)), (33, (1 / 6)), (39, (-1 / 2)), (54, (1 / 6))]

def value1689 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 288)), (2, (-1 / 32)), (3, (-2 / 9)), (7, (-1 / 18)), (26, (-1 / 18)), (46, (-1 / 2)), (51, (1 / 6)), (103, (-1 / 2))]

def value1690 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (-1 / 32)), (3, (-2 / 9)), (4, (-2 / 9)), (26, (-1 / 6)), (31, (1 / 6)), (33, (1 / 6))]

def value1691 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (1 / 18)), (43, (-1 / 2)), (103, (-1 / 2)), (104, (-1 / 2))]

def value1692 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (51, (1 / 6)), (54, (1 / 6)), (97, (-1 / 2)), (124, (1 / 6)), (383, (-1 / 2))]

def value1693 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 32)), (2, (-1 / 288)), (3, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 3)), (38, (-1 / 2)), (54, (1 / 6)), (98, (-1 / 2))]

def value1694 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 32)), (2, (-1 / 288)), (3, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (51, (1 / 3)), (54, (1 / 2)), (100, (-1 / 2))]

def value1695 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 288)), (2, (-1 / 32)), (3, (1 / 6)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (38, (-1 / 2))]

def value1696 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 48)), (2, (-1 / 48)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-5 / 18)), (41, (-1 / 2))]

def value1697 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 144)), (2, (-1 / 36)), (3, (-1 / 6)), (7, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (51, (1 / 2)), (54, (1 / 6)), (95, (-1 / 2))]

def value1698 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (1 / 48)), (2, (-1 / 18)), (3, (-2 / 9)), (12, (-1 / 6)), (13, (-1 / 6)), (33, (1 / 6))]

def value1699 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-2 / 9)), (13, (-7 / 18)), (59, (1 / 6)), (94, (-1 / 2))]

def value1700 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (17 / 288)), (2, (-1 / 72)), (3, (-2 / 9)), (12, (-2 / 9)), (13, (-1 / 18)), (95, (-1 / 2)), (102, (-1 / 2))]

def value1701 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 32)), (2, (-1 / 48)), (3, (-7 / 18)), (12, (-2 / 9)), (13, (-4 / 9)), (33, (1 / 6))]

def value1702 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 144)), (3, (-2 / 9)), (12, (-1 / 9)), (13, (-5 / 18)), (33, (1 / 6)), (38, (-1 / 2)), (54, (1 / 6))]

def value1703 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (41, (-1 / 2)), (95, (-1 / 2)), (103, (-1 / 2))]

def value1704 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 32)), (2, (-7 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (26, (-1 / 9)), (33, (1 / 6)), (41, (-1 / 2))]

def value1705 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 144)), (2, (-5 / 288)), (3, (-2 / 9)), (7, (-1 / 6)), (24, (1 / 6)), (51, (1 / 6)), (94, (-1 / 2)), (95, (-1 / 2))]

def value1706 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (-1 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (51, (1 / 6)), (54, (1 / 3)), (94, (-1 / 2)), (104, (-1 / 2))]

def value1707 : Sparse (Fin 909) := [(1, (-7 / 288)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 9)), (13, (-1 / 18)), (35, (-1 / 3)), (52, (-2 / 9)), (60, (-1 / 6)), (69, (-1 / 18)), (128, (-1 / 18)), (260, (1 / 6))]

def value1708 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 32)), (2, (-11 / 288)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (99, (-1 / 2)), (126, (1 / 6)), (400, (-1 / 2))]

def value1709 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (8, (-1 / 18)), (24, (1 / 3)), (39, (-1 / 2)), (56, (1 / 6)), (99, (-1 / 2))]

def value1710 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (2, (-7 / 288)), (3, (-5 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 18)), (33, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6)), (100, (-1 / 2))]

def value1711 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (31, (1 / 6)), (42, (-1 / 2)), (97, (-1 / 2)), (99, (-1 / 2))]

def value1712 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-5 / 288)), (3, (-1 / 9)), (52, (-1 / 18)), (98, (-1 / 2)), (99, (-1 / 2)), (237, (1 / 6)), (398, (-1 / 2))]

def value1713 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-5 / 18)), (52, (-1 / 6)), (60, (-1 / 6)), (128, (-1 / 18)), (392, (-1 / 2))]

def value1714 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 24)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (35, (-1 / 6)), (52, (-1 / 18)), (60, (-1 / 18)), (392, (-1 / 2))]

def value1715 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (13 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (8, (-1 / 18)), (39, (-1 / 2))]

def value1716 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (11 / 288)), (2, (-1 / 48)), (3, (-1 / 6)), (5, (1 / 72)), (12, (-1 / 18)), (33, (1 / 3)), (54, (1 / 6))]

def value1717 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (5 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (6, (-1 / 288)), (13, (-5 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (54, (1 / 6)), (62, (1 / 3))]

def value1718 : Sparse (Fin 909) := [(0, (1 / 360)), (2, (-1 / 72)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (33, (1 / 3))]

def value1719 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 36)), (2, (-13 / 288)), (3, (-1 / 18)), (42, (-1 / 2))]

def value1720 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 72)), (2, (1 / 36)), (3, (-2 / 9)), (12, (-1 / 9)), (13, (-4 / 9))]

def value1721 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 6)), (103, (-1 / 2)), (398, (-1 / 2))]

def value1722 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 96)), (8, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-5 / 18)), (59, (1 / 6)), (60, (-1 / 18)), (128, (-1 / 9)), (399, (-1 / 2))]

def value1723 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (13, (-1 / 6)), (35, (-5 / 18)), (52, (-2 / 9)), (59, (1 / 6)), (60, (-2 / 9)), (128, (-1 / 6))]

def value1724 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 288)), (2, (-1 / 72)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (104, (-1 / 2))]

def value1725 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 6)), (67, (-1 / 18)), (425, (-1 / 2))]

def value1726 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 144)), (2, (-1 / 96)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 2)), (24, (1 / 6)), (27, (-1 / 24)), (55, (1 / 6)), (105, (-1 / 2))]

def value1727 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-1 / 32)), (3, (-1 / 9)), (5, (5 / 72)), (7, (-5 / 18)), (8, (-1 / 6)), (26, (-1 / 18)), (35, (-1 / 6)), (67, (-1 / 18)), (81, (1 / 6)), (428, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2880 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (5 / 72)), (2, (11 / 72)), (3, (2 / 3)), (5, (-7 / 36)), (6, (1 / 144)), (7, (2 / 9)), (8, (4 / 9)), (10, (-1 / 2)), (12, (1 / 6)), (13, (4 / 9)), (35, (2 / 9)), (52, (2 / 9)), (59, (-2 / 3)), (72, (1 / 2)), (75, (1 / 1)), (199, (-1 / 6))]

def value2881 : Sparse (Fin 909) := [(0, (-1 / 288)), (2, (5 / 48)), (3, (5 / 9)), (5, (-5 / 24)), (6, (1 / 96)), (7, (11 / 18)), (8, (5 / 18)), (10, (-1 / 2)), (12, (5 / 18)), (13, (1 / 3)), (35, (4 / 9)), (52, (2 / 9)), (59, (-2 / 3)), (73, (1 / 2)), (74, (1 / 2)), (75, (1 / 2)), (201, (-1 / 6))]

def value2882 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 36)), (2, (1 / 96)), (3, (5 / 9)), (7, (1 / 9)), (10, (-1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 2)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 6)), (55, (-2 / 3)), (77, (1 / 1)), (79, (1 / 2)), (228, (-1 / 3)), (277, (-1 / 6)), (290, (1 / 1)), (291, (3 / 2))]

def value2883 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (11 / 288)), (3, (1 / 9)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 9)), (9, (-1 / 36)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (27, (1 / 8)), (35, (1 / 18)), (51, (-1 / 6)), (55, (-1 / 3)), (69, (1 / 18)), (71, (1 / 18)), (228, (-1 / 3)), (277, (-1 / 6)), (290, (1 / 2))]

def value2884 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-5 / 288)), (2, (1 / 96)), (3, (4 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 12)), (35, (1 / 18)), (51, (-1 / 6)), (54, (-1 / 3)), (55, (-1 / 6)), (77, (1 / 2)), (228, (-1 / 6))]

def value2885 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 18)), (2, (13 / 144)), (3, (2 / 3)), (5, (-5 / 72)), (7, (7 / 18)), (8, (1 / 9)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (35, (1 / 9)), (51, (-2 / 3)), (54, (-1 / 3))]

def value2886 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 144)), (2, (13 / 96)), (3, (11 / 18)), (4, (1 / 6)), (5, (-5 / 36)), (6, (1 / 288)), (7, (1 / 6)), (8, (4 / 9)), (26, (1 / 9)), (51, (-5 / 6)), (56, (-2 / 3)), (77, (1 / 2)), (228, (-1 / 6))]

def value2887 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 48)), (2, (1 / 18)), (3, (8 / 9)), (4, (1 / 2)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 3)), (27, (1 / 24)), (51, (-1 / 2)), (54, (-1 / 3)), (55, (-1 / 3)), (56, (-2 / 3)), (77, (1 / 2)), (78, (1 / 1)), (228, (-1 / 2))]

def value2888 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-7 / 144)), (2, (19 / 144)), (3, (2 / 9)), (5, (-1 / 9)), (7, (1 / 9)), (8, (4 / 9)), (12, (1 / 9)), (23, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 3)), (51, (-2 / 3)), (54, (-1 / 3))]

def value2889 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 72)), (2, (11 / 72)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 9)), (7, (2 / 9)), (8, (1 / 3)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 6)), (51, (-2 / 3)), (56, (-1 / 3))]

def value2890 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-31 / 288)), (2, (1 / 18)), (3, (1 / 2)), (5, (-1 / 72)), (7, (1 / 9)), (10, (-1 / 6)), (12, (5 / 18)), (13, (2 / 9)), (23, (-1 / 3)), (24, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 8)), (33, (-1 / 3)), (51, (-1 / 3)), (55, (-1 / 3)), (79, (1 / 2)), (94, (1 / 2)), (122, (1 / 1)), (127, (-1 / 6)), (299, (1 / 1)), (300, (1 / 1))]

def value2891 : Sparse (Fin 909) := [(1, (-7 / 36)), (2, (1 / 72)), (3, (10 / 9)), (4, (4 / 9)), (10, (-1 / 2)), (12, (5 / 9)), (13, (4 / 9)), (23, (-1 / 3)), (24, (-2 / 3)), (27, (1 / 24)), (55, (-4 / 3)), (79, (1 / 2)), (80, (1 / 1))]

def value2892 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-19 / 288)), (2, (5 / 144)), (3, (1 / 2)), (5, (-1 / 18)), (7, (1 / 6)), (12, (2 / 9)), (23, (-2 / 3)), (24, (-1 / 3)), (26, (1 / 9)), (27, (1 / 6)), (51, (-1 / 3)), (54, (-1 / 2)), (55, (-2 / 3)), (65, (-1 / 3))]

def value2893 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-23 / 288)), (2, (7 / 72)), (3, (5 / 9)), (5, (-1 / 18)), (7, (1 / 3)), (12, (1 / 9)), (23, (-2 / 3)), (24, (-1 / 2)), (27, (5 / 24)), (51, (-1 / 3)), (55, (-1 / 3)), (122, (1 / 2))]

def value2894 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-3 / 16)), (2, (19 / 144)), (3, (2 / 9)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 1)), (27, (5 / 12)), (30, (-2 / 3)), (55, (-1 / 3))]

def value2895 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 72)), (2, (5 / 288)), (3, (7 / 18)), (5, (-1 / 12)), (6, (1 / 72)), (7, (2 / 3)), (8, (2 / 9)), (9, (-1 / 36)), (26, (1 / 9)), (35, (1 / 3)), (52, (1 / 9)), (69, (1 / 9)), (71, (1 / 9)), (228, (-1 / 3)), (256, (-1 / 3)), (277, (-1 / 6))]

def value2896 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (11 / 288)), (2, (5 / 36)), (3, (2 / 9)), (5, (-19 / 72)), (6, (1 / 12)), (7, (1 / 6)), (8, (1 / 9)), (9, (-1 / 9)), (35, (1 / 6)), (52, (1 / 2)), (69, (1 / 6)), (70, (1 / 18)), (71, (1 / 9)), (228, (-1 / 3)), (277, (-1 / 6)), (322, (1 / 2)), (818, (-1 / 6))]

def value2897 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 144)), (2, (5 / 32)), (3, (11 / 18)), (4, (1 / 9)), (5, (-7 / 36)), (6, (1 / 48)), (7, (4 / 9)), (8, (4 / 9)), (9, (-1 / 36)), (26, (1 / 9)), (35, (2 / 9)), (52, (1 / 3)), (69, (1 / 9)), (71, (1 / 9)), (81, (-1 / 1)), (228, (-1 / 3)), (256, (-1 / 3)), (277, (-1 / 6))]

def value2898 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (11 / 144)), (2, (13 / 72)), (3, (5 / 9)), (5, (-25 / 72)), (6, (19 / 288)), (7, (1 / 3)), (8, (1 / 6)), (9, (-1 / 12)), (13, (1 / 9)), (35, (1 / 2)), (52, (2 / 3)), (69, (2 / 9)), (70, (1 / 9)), (71, (1 / 9)), (201, (-1 / 3)), (327, (1 / 2)), (726, (-1 / 6)), (818, (-1 / 6))]

def value2899 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (13 / 288)), (2, (1 / 16)), (3, (5 / 18)), (5, (-7 / 72)), (6, (1 / 144)), (7, (2 / 9)), (9, (-1 / 18)), (35, (1 / 9)), (52, (1 / 6)), (69, (1 / 9)), (70, (1 / 9)), (81, (-1 / 3)), (256, (-1 / 3)), (322, (1 / 2)), (818, (-1 / 2))]

def value2900 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 36)), (2, (-1 / 72)), (3, (4 / 9)), (5, (-1 / 36)), (6, (1 / 72)), (7, (1 / 2)), (8, (1 / 9)), (10, (-1 / 6)), (26, (2 / 9)), (27, (1 / 24)), (35, (4 / 9)), (55, (-1 / 3)), (67, (1 / 9)), (228, (-2 / 3)), (273, (-1 / 3))]

def value2901 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-13 / 144)), (2, (7 / 288)), (3, (19 / 18)), (5, (-5 / 72)), (6, (1 / 144)), (7, (5 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (4 / 9)), (13, (2 / 3)), (26, (1 / 9)), (27, (1 / 24)), (34, (1 / 9)), (35, (2 / 3)), (51, (-1 / 3)), (52, (1 / 9)), (55, (-1 / 3)), (59, (-1 / 3)), (60, (2 / 9)), (228, (-1 / 3)), (273, (-1 / 3)), (311, (1 / 1))]

def value2902 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 288)), (2, (-7 / 288)), (3, (1 / 3)), (5, (-1 / 18)), (6, (1 / 96)), (7, (1 / 9)), (23, (-1 / 6)), (25, (-1 / 6)), (26, (1 / 9)), (35, (2 / 9)), (36, (1 / 1)), (54, (-2 / 3)), (72, (1 / 2)), (83, (1 / 1)), (199, (-1 / 6)), (228, (-1 / 3)), (312, (1 / 1)), (316, (1 / 1)), (321, (1 / 2)), (492, (-1 / 6))]

def value2903 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-7 / 144)), (2, (5 / 144)), (3, (1 / 3)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (5 / 18)), (24, (-1 / 6)), (26, (1 / 9)), (35, (4 / 9)), (37, (1 / 1)), (52, (1 / 6)), (73, (1 / 2)), (83, (1 / 1)), (84, (3 / 2)), (228, (-1 / 6)), (317, (1 / 1))]

def value2904 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 144)), (2, (7 / 144)), (3, (4 / 9)), (5, (-1 / 24)), (7, (1 / 6)), (10, (-1 / 6)), (12, (5 / 18)), (13, (4 / 9)), (23, (-1 / 6)), (35, (7 / 18)), (38, (1 / 1)), (52, (2 / 9)), (54, (-1 / 3)), (59, (-1 / 6)), (72, (1 / 2)), (73, (1 / 2)), (82, (1 / 18)), (84, (1 / 1)), (128, (1 / 18)), (199, (-1 / 6)), (201, (-1 / 6)), (313, (1 / 1)), (318, (1 / 1))]

def value2905 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 72)), (2, (1 / 9)), (3, (7 / 9)), (4, (2 / 9)), (5, (-11 / 72)), (6, (7 / 288)), (7, (7 / 18)), (8, (2 / 9)), (10, (-1 / 6)), (26, (1 / 3)), (27, (1 / 24)), (35, (4 / 9)), (52, (1 / 3)), (55, (-1 / 3)), (67, (1 / 9)), (81, (-1 / 1)), (228, (-2 / 3)), (273, (-1 / 3))]

def value2906 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 288)), (2, (31 / 288)), (3, (11 / 18)), (4, (2 / 9)), (5, (-7 / 72)), (6, (1 / 288)), (7, (1 / 6)), (8, (2 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 6)), (33, (-2 / 3)), (34, (1 / 9)), (35, (1 / 18)), (51, (-1 / 3)), (52, (1 / 6)), (55, (-1 / 3)), (59, (-1 / 3)), (81, (-2 / 3)), (228, (-1 / 3)), (273, (-1 / 3)), (311, (1 / 2)), (314, (1 / 1)), (490, (-1 / 2))]

def value2907 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (11 / 144)), (2, (13 / 96)), (3, (2 / 9)), (4, (1 / 18)), (5, (-2 / 9)), (6, (5 / 288)), (7, (1 / 6)), (8, (5 / 18)), (13, (1 / 9)), (24, (-1 / 6)), (35, (1 / 18)), (39, (1 / 1)), (51, (-1 / 6)), (52, (1 / 6)), (56, (-1 / 3)), (59, (-1 / 6)), (74, (1 / 2)), (85, (1 / 1)), (128, (1 / 18)), (201, (-1 / 6)), (315, (1 / 1)), (319, (1 / 1))]

def value2908 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 288)), (2, (-1 / 18)), (3, (4 / 9)), (5, (-1 / 36)), (6, (5 / 288)), (7, (1 / 18)), (8, (1 / 9)), (26, (1 / 9)), (35, (1 / 3)), (83, (1 / 2)), (228, (-1 / 3))]

def value2909 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 36)), (2, (23 / 288)), (3, (4 / 9)), (5, (-1 / 8)), (7, (1 / 2)), (8, (1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (35, (11 / 18)), (51, (-1 / 6)), (52, (5 / 18)), (59, (-1 / 6)), (60, (1 / 18)), (81, (-1 / 6)), (84, (1 / 2)), (311, (1 / 2))]

def value2910 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 96)), (2, (17 / 144)), (3, (1 / 6)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 96)), (7, (2 / 9)), (8, (1 / 9)), (26, (1 / 18)), (35, (1 / 18)), (52, (1 / 6)), (81, (-1 / 3)), (85, (1 / 2)), (228, (-1 / 6))]

def value2911 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (5 / 96)), (3, (1 / 2)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 96)), (7, (13 / 18)), (8, (1 / 9)), (26, (1 / 9)), (35, (7 / 9)), (52, (7 / 18)), (84, (1 / 2)), (228, (-1 / 6))]

def value2912 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-5 / 96)), (2, (5 / 72)), (3, (1 / 1)), (5, (-1 / 18)), (7, (5 / 18)), (8, (1 / 18)), (10, (-1 / 2)), (12, (5 / 9)), (13, (8 / 9)), (33, (-1 / 6)), (35, (4 / 9)), (51, (-1 / 6)), (52, (5 / 18)), (54, (-1 / 6)), (59, (-2 / 3)), (60, (1 / 18)), (74, (1 / 2)), (75, (1 / 2)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 6)), (201, (-1 / 6)), (311, (1 / 2)), (313, (1 / 2))]

def value2913 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (11 / 144)), (2, (25 / 144)), (3, (5 / 18)), (5, (-13 / 36)), (6, (11 / 288)), (7, (7 / 18)), (8, (7 / 18)), (26, (1 / 18)), (35, (1 / 6)), (52, (2 / 9)), (85, (1 / 2)), (228, (-1 / 6))]

def value2914 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (2 / 9)), (3, (1 / 2)), (4, (1 / 9)), (5, (-19 / 72)), (6, (1 / 72)), (7, (5 / 18)), (8, (7 / 18)), (26, (1 / 9)), (35, (1 / 9)), (52, (5 / 18)), (81, (-1 / 3)), (85, (1 / 2)), (86, (1 / 2)), (228, (-1 / 6))]

def value2915 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (5 / 36)), (2, (55 / 288)), (3, (4 / 9)), (4, (1 / 9)), (5, (-19 / 72)), (6, (5 / 288)), (7, (2 / 9)), (8, (4 / 9)), (12, (1 / 18)), (13, (5 / 18)), (33, (-1 / 3)), (51, (-2 / 3)), (52, (7 / 18)), (56, (-1 / 6)), (59, (-1 / 2)), (76, (1 / 2)), (81, (-1 / 6)), (128, (1 / 9)), (201, (-1 / 6)), (314, (1 / 2)), (315, (1 / 2)), (326, (1 / 2)), (490, (-1 / 6))]

def value2916 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 24)), (3, (1 / 3)), (4, (1 / 9)), (5, (-5 / 72)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 18)), (33, (-1 / 3)), (35, (1 / 9)), (39, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (54, (-1 / 3)), (55, (-1 / 6)), (59, (-1 / 6)), (74, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (199, (-1 / 6)), (228, (-1 / 6)), (312, (1 / 2)), (314, (1 / 2)), (329, (1 / 2)), (330, (3 / 2)), (490, (-1 / 6)), (492, (-1 / 6))]

def value2917 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 32)), (2, (37 / 288)), (3, (7 / 9)), (4, (1 / 6)), (5, (-2 / 9)), (6, (1 / 96)), (7, (4 / 9)), (8, (1 / 3)), (11, (1 / 18)), (26, (1 / 3)), (33, (-1 / 6)), (35, (4 / 9)), (51, (-1 / 6)), (52, (2 / 9)), (59, (-1 / 6)), (81, (-1 / 2)), (83, (1 / 2)), (85, (1 / 1)), (228, (-2 / 3)), (314, (1 / 2)), (490, (-1 / 6))]

def value2918 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (31 / 288)), (3, (17 / 18)), (4, (5 / 18)), (5, (-5 / 36)), (6, (1 / 96)), (7, (5 / 18)), (8, (2 / 9)), (26, (4 / 9)), (35, (2 / 9)), (52, (1 / 9)), (81, (-2 / 3)), (83, (1 / 2)), (85, (1 / 1)), (228, (-2 / 3))]

def value2919 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 8)), (3, (5 / 9)), (4, (1 / 18)), (5, (-5 / 24)), (6, (1 / 48)), (7, (4 / 9)), (8, (2 / 9)), (26, (1 / 18)), (35, (2 / 3)), (52, (1 / 2)), (81, (-1 / 3)), (84, (1 / 2)), (228, (-1 / 6))]

def value2920 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (41 / 288)), (2, (55 / 288)), (3, (5 / 18)), (5, (-4 / 9)), (6, (13 / 288)), (7, (1 / 3)), (8, (2 / 3)), (35, (1 / 6)), (52, (2 / 9)), (81, (-1 / 3))]

def value2921 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (13 / 288)), (2, (17 / 72)), (3, (4 / 9)), (5, (-7 / 18)), (6, (1 / 32)), (7, (11 / 18)), (8, (4 / 9)), (35, (7 / 18)), (52, (7 / 18)), (86, (1 / 2))]

def value2922 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-13 / 288)), (2, (1 / 8)), (3, (7 / 9)), (4, (5 / 18)), (5, (-5 / 36)), (6, (1 / 144)), (7, (4 / 9)), (8, (1 / 9)), (26, (1 / 3)), (35, (1 / 2)), (52, (7 / 18)), (81, (-1 / 3)), (84, (1 / 2)), (85, (1 / 1)), (228, (-1 / 2))]

def value2923 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 48)), (2, (1 / 48)), (3, (5 / 18)), (4, (1 / 6)), (7, (1 / 6)), (12, (1 / 18)), (25, (-1 / 2)), (26, (1 / 3)), (35, (2 / 9)), (38, (3 / 2)), (52, (1 / 18)), (54, (-1 / 2)), (84, (3 / 2)), (228, (-1 / 2)), (321, (3 / 2)), (323, (1 / 1)), (492, (-1 / 6))]

def value2924 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (1 / 288)), (2, (7 / 96)), (3, (1 / 1)), (5, (-5 / 72)), (6, (1 / 144)), (7, (1 / 3)), (12, (1 / 3)), (13, (5 / 9)), (31, (-1 / 2)), (33, (-1 / 1)), (35, (5 / 9)), (52, (1 / 6)), (60, (2 / 9)), (81, (-1 / 1)), (311, (3 / 2)), (490, (-1 / 2))]

def value2925 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 48)), (2, (-7 / 144)), (3, (5 / 9)), (5, (-5 / 72)), (6, (1 / 36)), (7, (1 / 2)), (8, (2 / 9)), (9, (-1 / 72)), (25, (-1 / 6)), (26, (2 / 9)), (35, (1 / 3)), (54, (-1 / 3)), (69, (1 / 18)), (228, (-2 / 3)), (321, (1 / 2)), (492, (-1 / 6))]

def value2926 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 24)), (2, (1 / 9)), (3, (8 / 9)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 3)), (12, (1 / 3)), (13, (4 / 9)), (35, (5 / 9)), (52, (4 / 9)), (73, (1 / 2)), (75, (1 / 1)), (201, (-1 / 2))]

def value2927 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 12)), (2, (25 / 144)), (3, (1 / 3)), (4, (1 / 18)), (5, (-7 / 24)), (6, (1 / 36)), (7, (5 / 18)), (8, (4 / 9)), (35, (1 / 18)), (51, (-1 / 2)), (52, (2 / 9)), (322, (1 / 2)), (325, (1 / 1)), (327, (1 / 1)), (818, (-1 / 6))]

def value2928 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 96)), (2, (37 / 144)), (3, (5 / 9)), (5, (-19 / 72)), (6, (1 / 96)), (7, (5 / 18)), (8, (1 / 3)), (35, (5 / 18)), (52, (5 / 9)), (81, (-1 / 3)), (86, (1 / 1))]

def value2929 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 48)), (2, (7 / 48)), (3, (11 / 18)), (4, (1 / 9)), (5, (-1 / 12)), (6, (1 / 288)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 6)), (13, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 3)), (42, (1 / 1)), (51, (-1 / 3)), (52, (5 / 18)), (59, (-1 / 6)), (81, (-1 / 3)), (86, (1 / 1)), (128, (1 / 18)), (311, (1 / 2)), (326, (1 / 1)), (328, (1 / 1)), (490, (-1 / 6))]

def value2930 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (19 / 288)), (2, (23 / 144)), (3, (2 / 3)), (4, (1 / 9)), (5, (-11 / 72)), (6, (1 / 144)), (7, (1 / 6)), (8, (2 / 9)), (10, (-1 / 6)), (12, (2 / 9)), (13, (5 / 9)), (35, (1 / 9)), (42, (1 / 1)), (51, (-1 / 3)), (52, (4 / 9)), (59, (-1 / 2)), (82, (1 / 18)), (86, (1 / 1)), (128, (1 / 6)), (326, (1 / 1)), (328, (1 / 1))]

def value2931 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (7 / 72)), (3, (2 / 3)), (4, (1 / 18)), (5, (-1 / 12)), (6, (1 / 288)), (7, (1 / 6)), (8, (1 / 9)), (10, (-1 / 6)), (12, (2 / 9)), (13, (4 / 9)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 6)), (39, (1 / 1)), (51, (-1 / 6)), (52, (5 / 18)), (54, (-1 / 3)), (59, (-1 / 3)), (82, (1 / 18)), (85, (1 / 1)), (128, (1 / 9)), (228, (-1 / 3)), (321, (1 / 2)), (329, (1 / 1)), (330, (1 / 1)), (492, (-1 / 6))]

def value2932 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (1 / 24)), (3, (13 / 18)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (2 / 9)), (13, (1 / 9)), (25, (-1 / 6)), (26, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 3)), (35, (1 / 9)), (39, (1 / 1)), (52, (1 / 18)), (54, (-1 / 3)), (55, (-1 / 6)), (81, (-1 / 3)), (85, (1 / 1)), (228, (-1 / 3)), (311, (1 / 2)), (321, (1 / 2)), (329, (1 / 1)), (330, (1 / 1)), (490, (-1 / 6)), (492, (-1 / 6))]

def value2933 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 72)), (2, (11 / 96)), (3, (10 / 9)), (4, (4 / 9)), (5, (-1 / 18)), (7, (7 / 18)), (11, (1 / 18)), (26, (5 / 9)), (31, (-1 / 6)), (33, (-1 / 3)), (35, (1 / 2)), (52, (5 / 18)), (81, (-2 / 3)), (84, (1 / 2)), (85, (1 / 1)), (228, (-2 / 3)), (311, (1 / 2)), (490, (-1 / 6))]

def value2934 : Sparse (Fin 909) := [(0, (-1 / 288)), (2, (35 / 288)), (3, (5 / 9)), (5, (-13 / 72)), (6, (1 / 72)), (7, (1 / 2)), (8, (1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (24, (-1 / 6)), (35, (5 / 18)), (51, (-1 / 3)), (52, (5 / 18)), (73, (1 / 2)), (201, (-1 / 6)), (322, (3 / 2)), (327, (1 / 1)), (818, (-1 / 6))]

def value2935 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 32)), (2, (5 / 48)), (3, (5 / 9)), (5, (-5 / 24)), (6, (7 / 288)), (7, (1 / 2)), (8, (1 / 9)), (12, (1 / 18)), (13, (1 / 9)), (35, (13 / 18)), (52, (5 / 9)), (73, (1 / 2)), (81, (-1 / 3)), (201, (-1 / 6))]

def value2936 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (17 / 288)), (2, (1 / 12)), (3, (2 / 9)), (5, (-1 / 8)), (6, (17 / 288)), (8, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (13, (5 / 18)), (35, (1 / 9)), (52, (5 / 9)), (54, (-1 / 6)), (71, (1 / 18)), (82, (1 / 18)), (128, (1 / 6)), (228, (-1 / 3)), (329, (1 / 2)), (492, (-1 / 6))]

def value2937 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (29 / 288)), (2, (31 / 288)), (3, (2 / 3)), (5, (-7 / 24)), (6, (5 / 96)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 9)), (13, (11 / 18)), (35, (5 / 9)), (52, (5 / 6)), (82, (1 / 6)), (128, (2 / 9)), (201, (-1 / 3)), (328, (1 / 2))]

def value2938 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 72)), (2, (17 / 72)), (3, (5 / 9)), (5, (-1 / 3)), (6, (1 / 36)), (7, (5 / 18)), (8, (7 / 18)), (12, (1 / 18)), (13, (1 / 9)), (35, (2 / 9)), (52, (4 / 9)), (75, (1 / 2)), (86, (1 / 2)), (201, (-1 / 6))]

def value2939 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 96)), (2, (1 / 18)), (3, (7 / 18)), (5, (-11 / 72)), (6, (1 / 48)), (7, (2 / 3)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (23, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 6)), (69, (5 / 18)), (70, (1 / 18)), (71, (2 / 9)), (124, (-2 / 3)), (196, (-1 / 6)), (197, (-1 / 6)), (236, (-1 / 3)), (290, (1 / 2))]

def value2940 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 96)), (2, (13 / 288)), (3, (1 / 2)), (5, (-7 / 72)), (6, (1 / 288)), (7, (7 / 18)), (8, (1 / 6)), (12, (2 / 9)), (13, (2 / 9)), (35, (1 / 6)), (51, (-1 / 3)), (52, (1 / 18)), (59, (-1 / 6)), (69, (1 / 18)), (71, (1 / 18)), (105, (1 / 2)), (124, (-1 / 6)), (236, (-1 / 6)), (256, (-1 / 6)), (352, (1 / 2))]

def value2941 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (7 / 288)), (2, (17 / 288)), (3, (11 / 18)), (5, (-7 / 72)), (7, (4 / 9)), (8, (1 / 18)), (12, (1 / 6)), (13, (7 / 18)), (23, (-1 / 2)), (35, (4 / 9)), (52, (5 / 18)), (54, (-1 / 6)), (59, (-1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (98, (1 / 2)), (125, (-1 / 1)), (126, (-1 / 3)), (256, (-1 / 6)), (287, (1 / 2)), (352, (1 / 2))]

def value2942 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 48)), (2, (3 / 16)), (3, (5 / 6)), (5, (-1 / 6)), (6, (1 / 144)), (7, (1 / 9)), (8, (2 / 9)), (12, (1 / 3)), (13, (2 / 3)), (35, (2 / 9)), (51, (-1 / 6)), (52, (4 / 9)), (59, (-1 / 3)), (102, (1 / 1)), (201, (-1 / 6)), (256, (-1 / 6)), (327, (1 / 2)), (352, (1 / 2)), (818, (-1 / 6))]

def value2943 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 36)), (2, (1 / 32)), (3, (5 / 18)), (5, (-1 / 24)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (27, (1 / 8)), (35, (1 / 9)), (55, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1728 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 36)), (2, (-13 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 6)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (107, (-1 / 2))]

def value1729 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (19 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (12, (-1 / 18)), (25, (1 / 6)), (31, (1 / 6)), (100, (-1 / 2)), (105, (-1 / 2))]

def value1730 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 144)), (2, (-7 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 9)), (26, (-1 / 9)), (81, (1 / 6)), (107, (-1 / 2))]

def value1731 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (3, (-1 / 9)), (4, (-1 / 6)), (31, (1 / 6)), (106, (-1 / 2)), (107, (-1 / 2))]

def value1732 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (11 / 288)), (2, (-1 / 288)), (31, (1 / 6)), (45, (-1 / 2)), (105, (-1 / 2)), (107, (-1 / 2))]

def value1733 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (31, (1 / 6)), (46, (-1 / 2)), (97, (-1 / 2)), (106, (-1 / 2))]

def value1734 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 144)), (2, (-1 / 96)), (3, (-1 / 18)), (7, (-1 / 18)), (23, (1 / 6)), (24, (1 / 3)), (27, (-1 / 24)), (106, (-1 / 2)), (122, (-1 / 2))]

def value1735 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 32)), (2, (-7 / 288)), (5, (5 / 72)), (7, (-1 / 6)), (8, (-1 / 9)), (81, (1 / 3)), (307, (1 / 6)), (426, (-1 / 2))]

def value1736 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (3, (-1 / 9)), (4, (-1 / 9)), (5, (1 / 36)), (8, (-1 / 9)), (26, (-1 / 18)), (56, (1 / 6)), (107, (-1 / 2))]

def value1737 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 288)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 72)), (12, (-1 / 18)), (27, (-1 / 12)), (51, (1 / 6))]

def value1738 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (11 / 144)), (2, (-1 / 24)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 72)), (27, (-1 / 12)), (31, (1 / 3)), (51, (1 / 6))]

def value1739 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 288)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 6)), (5, (1 / 72)), (26, (-1 / 9)), (56, (1 / 6))]

def value1740 : Sparse (Fin 909) := [(0, (-17 / 1440)), (1, (1 / 18)), (2, (-1 / 32)), (3, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (45, (-1 / 2)), (51, (1 / 6))]

def value1741 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 6)), (7, (-1 / 18)), (31, (1 / 6)), (46, (-1 / 2)), (51, (1 / 6))]

def value1742 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 32)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (25, (1 / 6)), (26, (-1 / 18))]

def value1743 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (29 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (7, (-1 / 9)), (12, (-1 / 6)), (23, (1 / 6)), (24, (1 / 6))]

def value1744 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 32)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (25, (1 / 6)), (26, (-1 / 9)), (55, (1 / 6))]

def value1745 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (23 / 288)), (3, (-1 / 6)), (4, (-1 / 6)), (24, (1 / 6)), (26, (-1 / 18)), (44, (-1 / 2)), (55, (1 / 6))]

def value1746 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 9)), (2, (1 / 144)), (23, (1 / 6)), (25, (1 / 6)), (27, (-1 / 24))]

def value1747 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 32)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 6)), (27, (-1 / 24))]

def value1748 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (1 / 288)), (2, (-1 / 144)), (27, (-1 / 24)), (30, (1 / 6)), (31, (1 / 6))]

def value1749 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 144)), (2, (-7 / 288)), (3, (-1 / 6)), (12, (-1 / 6)), (23, (1 / 6)), (27, (-1 / 24))]

def value1750 : Sparse (Fin 909) := [(0, (-1 / 45)), (1, (13 / 144)), (2, (-5 / 144)), (27, (-1 / 24)), (30, (1 / 6))]

def value1751 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 48)), (2, (-1 / 48)), (3, (-1 / 9)), (4, (-1 / 6)), (24, (1 / 6)), (27, (-1 / 24)), (31, (1 / 6))]

def value1752 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (23, (1 / 6)), (25, (1 / 3)), (27, (-1 / 24)), (31, (1 / 3))]

def value1753 : Sparse (Fin 909) := [(1, (17 / 288)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 6)), (23, (1 / 6)), (26, (-1 / 18)), (43, (-1 / 2)), (55, (1 / 6))]

def value1754 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 36)), (7, (-2 / 9)), (26, (-1 / 6)), (35, (-4 / 9)), (67, (-2 / 9)), (81, (1 / 6))]

def value1755 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 18)), (7, (-1 / 6)), (24, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (95, (-1 / 2)), (453, (-1 / 2))]

def value1756 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 96)), (2, (-1 / 144)), (4, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (113, (-1 / 2))]

def value1757 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (25, (1 / 6)), (43, (-1 / 2)), (55, (1 / 6)), (104, (-1 / 2))]

def value1758 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 96)), (2, (-1 / 96)), (3, (-7 / 18)), (4, (-2 / 9)), (7, (-1 / 6)), (26, (-5 / 18)), (35, (-1 / 6)), (81, (1 / 6))]

def value1759 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-2 / 9)), (4, (-1 / 6)), (12, (-1 / 18)), (24, (1 / 6)), (44, (-1 / 2)), (55, (1 / 6)), (95, (-1 / 2))]

def value1760 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (55, (1 / 3)), (113, (-1 / 2)), (122, (-1 / 2))]

def value1761 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-1 / 9)), (12, (-1 / 6)), (43, (-1 / 2)), (95, (-1 / 2)), (113, (-1 / 2))]

def value1762 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 9)), (7, (-1 / 18)), (51, (1 / 6)), (95, (-1 / 2)), (104, (-1 / 2)), (472, (-1 / 2))]

def value1763 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-2 / 9)), (67, (-1 / 9)), (81, (1 / 6)), (307, (1 / 6)), (425, (-1 / 2))]

def value1764 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 9)), (26, (-5 / 18)), (35, (-1 / 3)), (52, (-1 / 9)), (67, (-1 / 6)), (460, (-1 / 2))]

def value1765 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (1 / 288)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 9)), (54, (1 / 6)), (64, (1 / 3))]

def value1766 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (13 / 288)), (2, (-5 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 6)), (43, (-1 / 2))]

def value1767 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-5 / 144)), (3, (-5 / 18)), (4, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 6)), (67, (-1 / 18)), (81, (1 / 6)), (460, (-1 / 2))]

def value1768 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 288)), (3, (-1 / 3)), (4, (-1 / 6)), (26, (-2 / 9))]

def value1769 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (37 / 288)), (2, (-5 / 288)), (3, (-7 / 18)), (4, (-1 / 18)), (12, (-1 / 3)), (13, (-1 / 18)), (33, (1 / 6))]

def value1770 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 36)), (2, (-11 / 288)), (3, (-7 / 18)), (4, (-2 / 9)), (5, (1 / 72)), (26, (-1 / 6)), (52, (-1 / 18)), (81, (1 / 6))]

def value1771 : Sparse (Fin 909) := [(0, (-11 / 720)), (1, (7 / 72)), (2, (-5 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (31, (1 / 3))]

def value1772 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 96)), (2, (-11 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (45, (-1 / 2))]

def value1773 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 16)), (2, (-1 / 36)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (46, (-1 / 2))]

def value1774 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (25 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-2 / 9)), (25, (1 / 6)), (26, (-1 / 18)), (31, (1 / 3))]

def value1775 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (13 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (46, (-1 / 2)), (51, (1 / 6)), (122, (-1 / 2))]

def value1776 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 48)), (3, (-1 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (31, (1 / 6)), (43, (-1 / 2))]

def value1777 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 288)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-1 / 9)), (33, (1 / 6)), (52, (-1 / 18)), (59, (1 / 6)), (81, (1 / 6)), (307, (1 / 6)), (428, (-1 / 2))]

def value1778 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (26, (-1 / 6)), (33, (1 / 6)), (35, (-2 / 9)), (52, (-1 / 18)), (59, (1 / 6)), (67, (-1 / 9)), (307, (1 / 6)), (428, (-1 / 2))]

def value1779 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 3)), (4, (-1 / 9)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-7 / 18)), (34, (-1 / 6)), (35, (-1 / 6)), (67, (-1 / 6)), (453, (-1 / 2))]

def value1780 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 144)), (2, (-5 / 288)), (3, (-1 / 3)), (4, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 3)), (26, (-1 / 9)), (33, (1 / 6)), (64, (1 / 6))]

def value1781 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (17 / 288)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 6)), (25, (1 / 6)), (26, (-1 / 18)), (43, (-1 / 2))]

def value1782 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-1 / 9)), (12, (-1 / 6)), (43, (-1 / 1)), (116, (-1 / 2))]

def value1783 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-1 / 3)), (4, (-1 / 6)), (26, (-2 / 9)), (119, (-1 / 2)), (460, (-1 / 2))]

def value1784 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 72)), (3, (-1 / 3)), (4, (-2 / 9)), (12, (-1 / 18)), (26, (-1 / 6)), (44, (-1 / 2))]

def value1785 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (-1 / 36)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (25, (1 / 6))]

def value1786 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (1 / 12)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-2 / 9))]

def value1787 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (1 / 12)), (2, (-1 / 288)), (3, (-4 / 9)), (4, (-1 / 9)), (12, (-5 / 18)), (13, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 18)), (33, (1 / 3)), (34, (-1 / 18))]

def value1788 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-4 / 9)), (4, (-2 / 9)), (7, (-1 / 18)), (26, (-1 / 3)), (33, (1 / 6)), (34, (-1 / 18)), (35, (-1 / 9)), (67, (-1 / 18)), (81, (1 / 3))]

def value1789 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (5 / 144)), (2, (-11 / 288)), (3, (-5 / 18)), (4, (-2 / 9)), (26, (-1 / 18)), (31, (1 / 6))]

def value1790 : Sparse (Fin 909) := [(0, (-13 / 480)), (1, (25 / 288)), (2, (-5 / 144)), (31, (1 / 6))]

def value1791 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 48)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 6)), (25, (1 / 6)), (33, (1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1792 : Sparse (Fin 909) := [(0, (-5 / 288)), (1, (7 / 96)), (2, (-1 / 36)), (3, (-1 / 18)), (4, (-1 / 18)), (31, (1 / 6)), (45, (-1 / 2))]

def value1793 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (7 / 96)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-2 / 9)), (12, (-1 / 18)), (31, (1 / 6))]

def value1794 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 288)), (2, (-1 / 72)), (3, (-1 / 3)), (4, (-2 / 9)), (26, (-1 / 6)), (31, (1 / 6)), (33, (1 / 6)), (34, (-1 / 18)), (119, (-1 / 2))]

def value1795 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (44, (-1 / 2)), (45, (-1 / 2)), (120, (-1 / 2))]

def value1796 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 24)), (2, (-1 / 288)), (3, (-1 / 2)), (4, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-5 / 18)), (34, (-1 / 6)), (119, (-1 / 2))]

def value1797 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 32)), (2, (-1 / 288)), (3, (-1 / 3)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 6)), (33, (1 / 6)), (34, (-1 / 9)), (64, (1 / 6)), (112, (-1 / 2))]

def value1798 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 288)), (2, (-1 / 32)), (3, (-1 / 9)), (25, (1 / 6)), (31, (1 / 6)), (33, (1 / 3)), (64, (1 / 6)), (112, (-1 / 2))]

def value1799 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (43, (-1 / 2)), (46, (-1 / 2)), (116, (-1 / 2))]

def value1800 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (23 / 288)), (2, (-1 / 72)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 9)), (25, (1 / 3)), (31, (1 / 6))]

def value1801 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (23 / 288)), (2, (-5 / 288)), (3, (-2 / 9)), (4, (-1 / 6)), (12, (-1 / 18)), (31, (1 / 6)), (46, (-1 / 2))]

def value1802 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 36)), (2, (-1 / 48)), (3, (-2 / 9)), (12, (-1 / 9)), (25, (1 / 6)), (33, (1 / 3)), (81, (1 / 6)), (122, (-1 / 2))]

def value1803 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (2, (-11 / 288)), (3, (-2 / 9)), (12, (-1 / 9)), (25, (1 / 6)), (31, (1 / 6)), (33, (1 / 6))]

def value1804 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 9)), (33, (1 / 6)), (43, (-1 / 2))]

def value1805 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 144)), (2, (-13 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (33, (1 / 2)), (64, (1 / 6)), (81, (1 / 3)), (307, (1 / 6))]

def value1806 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 144)), (2, (-7 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (26, (-1 / 9)), (33, (1 / 3)), (112, (-1 / 2)), (428, (-1 / 2))]

def value1807 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-2 / 9)), (4, (-1 / 18)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-2 / 9)), (33, (1 / 6)), (34, (-1 / 9)), (35, (-1 / 9)), (64, (1 / 6)), (67, (-1 / 9)), (307, (1 / 6)), (472, (-1 / 2))]

def value1808 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (12, (-1 / 6)), (23, (1 / 6)), (25, (1 / 6)), (33, (1 / 6)), (43, (-1 / 2)), (110, (-1 / 2))]

def value1809 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (25, (1 / 3)), (33, (1 / 6)), (50, (-1 / 2)), (116, (-1 / 2))]

def value1810 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 6)), (33, (1 / 6)), (34, (-1 / 18)), (114, (-1 / 2))]

def value1811 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 16)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-2 / 9)), (33, (1 / 6)), (45, (-1 / 2)), (115, (-1 / 2))]

def value1812 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 16)), (3, (-5 / 18)), (4, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 18)), (115, (-1 / 2)), (120, (-1 / 2))]

def value1813 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 24)), (2, (-1 / 144)), (3, (-7 / 18)), (4, (-1 / 18)), (12, (-1 / 6)), (13, (-2 / 9)), (26, (-2 / 9)), (33, (1 / 6)), (34, (-2 / 9))]

def value1814 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-1 / 6)), (12, (-1 / 9)), (13, (-1 / 6)), (26, (-1 / 18)), (33, (1 / 6)), (34, (-1 / 9)), (64, (1 / 6)), (110, (-1 / 2))]

def value1815 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-1 / 9)), (12, (-1 / 6)), (50, (-1 / 2)), (115, (-1 / 2)), (116, (-1 / 2))]

def value1816 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (46, (-1 / 2)), (114, (-1 / 2)), (115, (-1 / 2))]

def value1817 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (11 / 288)), (2, (-7 / 288)), (3, (-7 / 18)), (4, (-1 / 9)), (7, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 3)), (34, (-1 / 6)), (64, (1 / 6))]

def value1818 : Sparse (Fin 909) := [(1, (11 / 144)), (2, (-1 / 144)), (3, (-4 / 9)), (4, (-2 / 9)), (12, (-1 / 18)), (25, (1 / 6)), (26, (-2 / 9))]

def value1819 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (25 / 288)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-2 / 9)), (25, (1 / 6)), (26, (-1 / 18)), (31, (1 / 6)), (44, (-1 / 2))]

def value1820 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 18)), (2, (-1 / 288)), (3, (-1 / 3)), (4, (-1 / 6)), (12, (-1 / 18)), (26, (-1 / 6)), (43, (-1 / 2))]

def value1821 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (13, (-1 / 18)), (26, (-5 / 18)), (34, (-1 / 6)), (116, (-1 / 2))]

def value1822 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 72)), (2, (-1 / 36)), (3, (-1 / 18)), (4, (-1 / 9)), (26, (-1 / 6)), (34, (-1 / 18)), (116, (-1 / 2))]

def value1823 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 144)), (2, (-1 / 72)), (25, (1 / 6)), (31, (1 / 3))]

def value1824 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-2 / 9)), (4, (-1 / 18)), (26, (-1 / 18)), (46, (-1 / 2))]

def value1825 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (11 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-2 / 9)), (31, (1 / 3))]

def value1826 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (7 / 72)), (2, (-1 / 72)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 6)), (26, (-1 / 18)), (45, (-1 / 2))]

def value1827 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (1 / 288)), (2, (-1 / 24)), (3, (-1 / 3)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 9)), (26, (-1 / 18)), (33, (1 / 6)), (34, (-1 / 18)), (120, (-1 / 2))]

def value1828 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-7 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 6)), (26, (-5 / 18)), (33, (1 / 6)), (34, (-2 / 9))]

def value1829 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (3, (-1 / 6)), (26, (-1 / 18)), (31, (1 / 6)), (43, (-1 / 2))]

def value1830 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (1 / 18)), (2, (-7 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (33, (1 / 6)), (45, (-1 / 2))]

def value1831 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (11 / 144)), (2, (-1 / 288)), (3, (-4 / 9)), (4, (-2 / 9)), (12, (-1 / 9)), (26, (-1 / 6)), (33, (1 / 6))]

def value1832 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (7, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (47, (-1 / 2)), (48, (-1 / 2)), (94, (-1 / 2))]

def value1833 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (47, (-1 / 2)), (51, (1 / 6))]

def value1834 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (7 / 96)), (2, (-1 / 144)), (3, (-2 / 9)), (4, (-1 / 6)), (12, (-1 / 9)), (13, (-1 / 18)), (31, (1 / 6)), (49, (-1 / 2)), (51, (1 / 6))]

def value1835 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 72)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (48, (-1 / 2)), (51, (1 / 6))]

def value1836 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (5 / 72)), (2, (-5 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (33, (1 / 6)), (49, (-1 / 2)), (51, (1 / 6))]

def value1837 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (13 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (31, (1 / 3)), (47, (-1 / 2)), (51, (1 / 6))]

def value1838 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 48)), (2, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (31, (1 / 6)), (33, (1 / 6)), (48, (-1 / 2)), (51, (1 / 6))]

def value1839 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 144)), (2, (-1 / 96)), (3, (-5 / 18)), (4, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (47, (-1 / 2))]

def value1840 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 32)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (25, (1 / 6)), (48, (-1 / 2))]

def value1841 : Sparse (Fin 909) := [(0, (-19 / 1440)), (1, (1 / 24)), (2, (-7 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (8, (-1 / 18)), (24, (1 / 6)), (30, (1 / 6)), (49, (-1 / 2))]

def value1842 : Sparse (Fin 909) := [(1, (35 / 288)), (2, (-1 / 288)), (3, (-7 / 18)), (4, (-2 / 9)), (12, (-2 / 9)), (13, (-1 / 18)), (24, (1 / 6)), (55, (1 / 6))]

def value1843 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 12)), (3, (-5 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (50, (-1 / 2))]

def value1844 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (3 / 32)), (3, (-4 / 9)), (4, (-1 / 6)), (12, (-2 / 9)), (13, (-1 / 6)), (33, (1 / 6))]

def value1845 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (5 / 96)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (25, (1 / 6)), (33, (1 / 6)), (50, (-1 / 2))]

def value1846 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (7 / 96)), (3, (-2 / 9)), (4, (-2 / 9)), (12, (-1 / 6)), (25, (1 / 6)), (50, (-1 / 2))]

def value1847 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (25 / 288)), (2, (-5 / 288)), (3, (-2 / 9)), (4, (-2 / 9)), (12, (-1 / 18)), (31, (1 / 3)), (33, (1 / 6))]

def value1848 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (3 / 32)), (2, (-1 / 96)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 9)), (25, (1 / 3)), (31, (1 / 3)), (33, (1 / 6))]

def value1849 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-1 / 96)), (2, (-5 / 48)), (3, (-1 / 6)), (5, (5 / 12)), (6, (-1 / 24)), (7, (-1 / 3)), (8, (-2 / 3)), (69, (-1 / 6)), (71, (-2 / 3)), (124, (1 / 2)), (126, (1 / 2)), (197, (1 / 2)), (236, (1 / 1))]

def value1850 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 12)), (2, (-17 / 96)), (3, (-2 / 3)), (5, (1 / 6)), (6, (-1 / 96)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-2 / 3)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-2 / 3)), (69, (-1 / 6)), (126, (1 / 2)), (128, (-1 / 6)), (262, (1 / 2)), (495, (-1 / 6))]

def value1851 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-1 / 48)), (2, (-13 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 12)), (7, (-1 / 3)), (8, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 3)), (59, (1 / 2)), (81, (1 / 2)), (256, (1 / 2)), (486, (-1 / 1))]

def value1852 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 48)), (2, (-1 / 12)), (3, (-5 / 6)), (5, (1 / 24)), (7, (-1 / 2)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 2)), (25, (1 / 2)), (26, (-1 / 6)), (35, (-1 / 6)), (51, (1 / 1)), (52, (-1 / 6)), (54, (1 / 1)), (64, (1 / 1)), (123, (1 / 2)), (124, (1 / 2)), (125, (1 / 2)), (259, (1 / 2)), (260, (1 / 2))]

def value1853 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 16)), (2, (-1 / 16)), (3, (-7 / 6)), (4, (-1 / 6)), (12, (-1 / 2)), (13, (-7 / 6)), (26, (-1 / 6)), (33, (1 / 2)), (34, (-1 / 3)), (35, (-1 / 6)), (51, (1 / 2)), (52, (-1 / 3)), (59, (1 / 2)), (60, (-1 / 6)), (128, (-1 / 6))]

def value1854 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (1 / 24)), (2, (-1 / 48)), (3, (-2 / 3)), (5, (1 / 3)), (6, (-1 / 16)), (12, (-1 / 6)), (13, (-2 / 3)), (52, (-2 / 3)), (128, (-1 / 6))]

def value1855 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 24)), (2, (-5 / 96)), (3, (-1 / 3)), (12, (-1 / 6)), (13, (-1 / 6)), (27, (-1 / 8)), (31, (1 / 2)), (33, (1 / 2)), (51, (1 / 1)), (52, (-1 / 6)), (59, (1 / 2)), (123, (1 / 2)), (124, (1 / 2)), (126, (1 / 2)), (259, (1 / 2)), (262, (1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2944 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 48)), (2, (1 / 16)), (3, (2 / 3)), (5, (-1 / 24)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (7 / 18)), (13, (4 / 9)), (27, (1 / 8)), (51, (-2 / 3)), (55, (-1 / 3)), (59, (-1 / 3))]

def value2945 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-73 / 288)), (2, (1 / 18)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 6)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 9)), (27, (1 / 8)), (31, (-1 / 6)), (35, (1 / 18)), (52, (1 / 18)), (55, (-1 / 3)), (95, (1 / 2))]

def value2946 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 9)), (2, (1 / 288)), (3, (11 / 18)), (5, (-1 / 18)), (6, (1 / 72)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 6)), (13, (5 / 9)), (33, (-1 / 3)), (35, (1 / 9)), (52, (2 / 9)), (54, (-1 / 3)), (59, (-1 / 3)), (199, (-1 / 6))]

def value2947 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (13 / 288)), (2, (-1 / 288)), (3, (2 / 9)), (5, (-1 / 12)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (23, (-1 / 3)), (26, (1 / 9)), (35, (2 / 9)), (36, (1 / 2)), (38, (1 / 2)), (54, (-1 / 3)), (55, (-1 / 6)), (72, (1 / 2))]

def value2948 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 288)), (2, (1 / 32)), (3, (7 / 18)), (4, (1 / 18)), (5, (-1 / 36)), (7, (2 / 9)), (8, (1 / 18)), (10, (-1 / 6)), (12, (1 / 9)), (13, (1 / 2)), (26, (1 / 18)), (35, (5 / 18)), (37, (1 / 2)), (41, (1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (59, (-1 / 6)), (73, (1 / 2))]

def value2949 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-37 / 288)), (2, (7 / 72)), (3, (5 / 6)), (4, (1 / 18)), (5, (-7 / 72)), (7, (4 / 9)), (8, (1 / 6)), (10, (-1 / 6)), (12, (1 / 3)), (13, (2 / 9)), (26, (1 / 9)), (35, (1 / 6)), (39, (1 / 2)), (51, (-2 / 3)), (54, (-1 / 3)), (55, (-1 / 6)), (74, (1 / 2)), (95, (1 / 2))]

def value2950 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-23 / 144)), (2, (43 / 288)), (3, (1 / 1)), (4, (1 / 9)), (5, (-5 / 72)), (7, (1 / 6)), (8, (1 / 9)), (10, (-1 / 6)), (12, (5 / 9)), (13, (5 / 9)), (26, (1 / 18)), (33, (-1 / 3)), (35, (1 / 9)), (40, (1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (59, (-1 / 6)), (75, (1 / 2))]

def value2951 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-7 / 144)), (2, (19 / 288)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (5 / 18)), (13, (5 / 18)), (26, (1 / 18)), (35, (1 / 18)), (40, (1 / 2)), (52, (1 / 18)), (55, (-1 / 6)), (59, (-1 / 6)), (75, (1 / 2)), (95, (1 / 2)), (102, (1 / 2))]

def value2952 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-1 / 16)), (2, (5 / 48)), (3, (7 / 9)), (4, (1 / 9)), (5, (-1 / 18)), (7, (1 / 3)), (8, (1 / 9)), (10, (-1 / 6)), (13, (2 / 9)), (24, (-1 / 3)), (26, (1 / 9)), (35, (1 / 9)), (38, (1 / 2)), (51, (-1 / 3)), (55, (-1 / 6)), (72, (1 / 2)), (94, (1 / 1)), (95, (1 / 1))]

def value2953 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 18)), (2, (1 / 16)), (3, (1 / 2)), (5, (-5 / 36)), (6, (1 / 32)), (7, (1 / 9)), (13, (4 / 9)), (35, (2 / 3)), (52, (1 / 2)), (54, (-1 / 6)), (60, (5 / 18)), (62, (-1 / 3)), (82, (1 / 18)), (128, (5 / 18)), (199, (-1 / 6)), (201, (-1 / 3)), (267, (-1 / 3)), (392, (1 / 2))]

def value2954 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (5 / 72)), (2, (13 / 144)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 8)), (6, (5 / 288)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 6)), (26, (1 / 9)), (33, (-1 / 3)), (35, (2 / 9)), (52, (7 / 18)), (59, (-1 / 3)), (103, (1 / 2)), (201, (-1 / 6))]

def value2955 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-7 / 288)), (2, (11 / 144)), (3, (8 / 9)), (5, (-1 / 9)), (6, (5 / 288)), (7, (1 / 18)), (8, (1 / 18)), (12, (4 / 9)), (13, (10 / 9)), (35, (5 / 18)), (52, (7 / 18)), (59, (-1 / 3)), (102, (1 / 2)), (201, (-1 / 6))]

def value2956 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (37 / 288)), (2, (41 / 288)), (3, (1 / 3)), (5, (-1 / 4)), (6, (1 / 24)), (8, (1 / 9)), (12, (1 / 9)), (13, (17 / 18)), (32, (1 / 9)), (35, (2 / 9)), (52, (8 / 9)), (59, (-1 / 3)), (60, (2 / 9)), (82, (1 / 9)), (128, (5 / 9)), (199, (-1 / 6)), (201, (-1 / 3)), (267, (-1 / 3)), (399, (1 / 1))]

def value2957 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (5 / 72)), (2, (1 / 8)), (3, (4 / 9)), (5, (-1 / 9)), (6, (1 / 144)), (8, (2 / 9)), (12, (1 / 6)), (13, (4 / 9)), (52, (2 / 9)), (59, (-2 / 3)), (102, (1 / 1)), (199, (-1 / 6))]

def value2958 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 288)), (2, (23 / 288)), (3, (1 / 2)), (5, (-1 / 9)), (7, (7 / 18)), (12, (1 / 18)), (13, (5 / 18)), (23, (-1 / 6)), (26, (1 / 18)), (35, (2 / 3)), (52, (1 / 3)), (54, (-1 / 6)), (69, (2 / 9)), (70, (2 / 9)), (125, (-2 / 3)), (126, (-1 / 3)), (256, (-1 / 6)), (291, (1 / 2)), (378, (1 / 2))]

def value2959 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 16)), (2, (-1 / 48)), (3, (1 / 9)), (5, (5 / 72)), (6, (1 / 72)), (7, (1 / 9)), (26, (1 / 9)), (27, (1 / 24)), (35, (1 / 9)), (55, (-1 / 3)), (87, (1 / 2)), (228, (-1 / 3))]

def value2960 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 144)), (5, (1 / 72)), (6, (1 / 72)), (7, (1 / 9)), (9, (-1 / 72)), (35, (1 / 9)), (52, (1 / 9)), (54, (-1 / 2)), (69, (1 / 9)), (199, (-1 / 3)), (228, (-1 / 3)), (260, (-1 / 3)), (271, (-1 / 3)), (492, (-1 / 6))]

def value2961 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 16)), (3, (4 / 9)), (5, (-1 / 9)), (6, (5 / 144)), (7, (1 / 9)), (13, (1 / 9)), (35, (5 / 9)), (52, (11 / 18)), (56, (-1 / 6)), (60, (1 / 9)), (128, (1 / 18)), (201, (-1 / 3)), (228, (-1 / 3)), (275, (-1 / 3))]

def value2962 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 18)), (2, (1 / 144)), (3, (5 / 9)), (5, (-1 / 9)), (6, (1 / 48)), (7, (1 / 6)), (12, (1 / 9)), (13, (1 / 2)), (26, (1 / 18)), (35, (1 / 3)), (52, (4 / 9)), (54, (-1 / 3)), (103, (1 / 2)), (228, (-1 / 6))]

def value2963 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (13 / 144)), (2, (1 / 9)), (3, (1 / 3)), (5, (-7 / 36)), (6, (1 / 24)), (7, (2 / 9)), (8, (2 / 9)), (12, (1 / 9)), (13, (1 / 2)), (35, (4 / 9)), (52, (5 / 9)), (54, (-1 / 6)), (59, (-1 / 1)), (60, (1 / 9)), (82, (1 / 18)), (128, (1 / 6)), (199, (-1 / 3)), (201, (-1 / 3)), (228, (-1 / 3)), (271, (-1 / 3))]

def value2964 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 18)), (2, (1 / 48)), (3, (7 / 18)), (5, (-1 / 18)), (7, (1 / 6)), (23, (-1 / 6)), (25, (-1 / 6)), (26, (2 / 9)), (27, (1 / 24)), (36, (1 / 2)), (54, (-1 / 3)), (55, (-1 / 6))]

def value2965 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-19 / 288)), (2, (1 / 12)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 36)), (8, (1 / 6)), (26, (1 / 18)), (27, (1 / 24)), (30, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (40, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value2966 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-11 / 144)), (2, (7 / 96)), (3, (19 / 18)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 2)), (13, (8 / 9)), (23, (-1 / 6)), (27, (1 / 24)), (38, (1 / 2)), (51, (-1 / 3)), (54, (-1 / 3)), (55, (-1 / 6))]

def value2967 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (-31 / 144)), (2, (17 / 144)), (3, (5 / 9)), (4, (1 / 9)), (5, (-1 / 36)), (8, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 18)), (27, (1 / 24)), (30, (-1 / 6)), (40, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value2968 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-65 / 288)), (2, (3 / 32)), (3, (17 / 18)), (4, (7 / 18)), (5, (-1 / 72)), (8, (1 / 18)), (12, (7 / 18)), (13, (1 / 3)), (24, (-1 / 6)), (27, (1 / 24)), (31, (-1 / 6)), (33, (-1 / 3)), (39, (1 / 2)), (42, (1 / 2)), (51, (-1 / 3)), (55, (-1 / 6)), (56, (-1 / 3))]

def value2969 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-11 / 72)), (2, (29 / 288)), (3, (8 / 9)), (4, (7 / 18)), (5, (-1 / 36)), (7, (1 / 6)), (24, (-1 / 6)), (26, (4 / 9)), (27, (1 / 24)), (31, (-1 / 6)), (33, (-1 / 3)), (37, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value2970 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 96)), (2, (-1 / 72)), (3, (1 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 9)), (12, (2 / 9)), (13, (2 / 9)), (23, (-1 / 6)), (26, (1 / 9)), (27, (1 / 24)), (38, (1 / 2)), (54, (-1 / 6)), (55, (-1 / 6))]

def value2971 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 32)), (2, (1 / 12)), (3, (5 / 18)), (5, (-1 / 36)), (8, (1 / 6)), (12, (1 / 9)), (33, (-1 / 3)), (39, (1 / 2)), (51, (-1 / 3)), (54, (-1 / 3))]

def value2972 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-5 / 48)), (2, (-1 / 144)), (3, (2 / 3)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 6)), (33, (-1 / 3)), (51, (-1 / 3)), (56, (-1 / 6))]

def value2973 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 18)), (2, (23 / 288)), (3, (2 / 9)), (4, (1 / 18)), (5, (-1 / 72)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 6)), (13, (1 / 6)), (42, (1 / 2)), (51, (-1 / 3)), (56, (-1 / 6))]

def value2974 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-19 / 96)), (2, (19 / 288)), (3, (7 / 9)), (5, (-1 / 72)), (8, (1 / 9)), (12, (5 / 18)), (13, (4 / 9)), (51, (-1 / 3)), (54, (-1 / 6))]

def value2975 : Sparse (Fin 909) := [(1, (-19 / 144)), (2, (7 / 144)), (3, (7 / 9)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (12, (4 / 9)), (13, (1 / 6)), (23, (-1 / 3)), (25, (-1 / 2)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 18)), (36, (1 / 2)), (39, (1 / 1)), (54, (-1 / 3)), (55, (-1 / 6)), (87, (1 / 1)), (100, (1 / 1))]

def value2976 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-5 / 32)), (2, (7 / 288)), (3, (5 / 6)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 9)), (26, (2 / 9)), (33, (-2 / 3)), (36, (1 / 2)), (40, (1 / 1)), (54, (-1 / 6)), (55, (-1 / 2))]

def value2977 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-55 / 288)), (2, (1 / 16)), (3, (1 / 1)), (4, (1 / 3)), (12, (1 / 3)), (13, (1 / 6)), (26, (1 / 3)), (33, (-1 / 3)), (37, (1 / 2)), (39, (1 / 2)), (40, (1 / 2)), (55, (-1 / 2))]

def value2978 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-19 / 96)), (2, (1 / 48)), (3, (7 / 9)), (4, (5 / 18)), (12, (1 / 2)), (13, (1 / 3)), (25, (-1 / 2)), (33, (-1 / 6)), (35, (1 / 18)), (38, (1 / 2)), (39, (1 / 1)), (51, (-1 / 3)), (52, (1 / 18)), (54, (-1 / 3)), (55, (-1 / 6)), (89, (1 / 1)), (104, (1 / 2))]

def value2979 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-25 / 144)), (2, (7 / 72)), (3, (8 / 9)), (4, (4 / 9)), (12, (2 / 9)), (13, (1 / 3)), (26, (2 / 9)), (38, (1 / 2)), (40, (1 / 1)), (55, (-1 / 2))]

def value2980 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 48)), (2, (1 / 16)), (3, (5 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (23, (-1 / 3)), (33, (-1 / 6)), (35, (2 / 9)), (52, (2 / 9)), (69, (1 / 9)), (70, (1 / 9)), (81, (-1 / 3)), (95, (1 / 1)), (124, (-1 / 3)), (196, (-1 / 3)), (256, (-1 / 6)), (322, (1 / 1)), (379, (3 / 2))]

def value2981 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-7 / 96)), (2, (-1 / 96)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 3)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (2 / 9)), (35, (2 / 9)), (54, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (97, (1 / 1)), (113, (1 / 2)), (124, (-1 / 3)), (197, (-1 / 3)), (291, (1 / 2)), (378, (1 / 1))]

def value2982 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 18)), (2, (1 / 18)), (3, (11 / 18)), (4, (1 / 18)), (5, (-1 / 24)), (7, (5 / 18)), (12, (2 / 9)), (13, (1 / 9)), (23, (-1 / 2)), (24, (-1 / 3)), (33, (-1 / 6)), (35, (1 / 6)), (52, (1 / 18)), (54, (-1 / 6)), (55, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (100, (1 / 1)), (104, (1 / 2)), (125, (-1 / 3)), (126, (-1 / 3)), (291, (1 / 2)), (379, (1 / 1))]

def value2983 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 72)), (2, (1 / 16)), (3, (1 / 9)), (5, (-1 / 12)), (6, (1 / 72)), (31, (-1 / 6)), (33, (-1 / 6)), (52, (1 / 9)), (81, (-1 / 3)), (95, (1 / 2)), (256, (-1 / 6)), (322, (1 / 2)), (379, (1 / 2)), (818, (-1 / 6))]

def value2984 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 36)), (2, (5 / 48)), (3, (7 / 18)), (4, (1 / 18)), (5, (-1 / 6)), (6, (1 / 72)), (7, (1 / 6)), (13, (1 / 6)), (26, (1 / 18)), (35, (1 / 3)), (51, (-1 / 6)), (52, (2 / 3)), (103, (1 / 1)), (256, (-1 / 6)), (322, (1 / 2)), (378, (1 / 2)), (818, (-1 / 6))]

def value2985 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 32)), (2, (5 / 72)), (3, (7 / 18)), (5, (-5 / 72)), (6, (1 / 144)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (31, (-1 / 2)), (33, (-1 / 3)), (35, (1 / 9)), (52, (1 / 6)), (81, (-1 / 3)), (95, (1 / 2))]

def value2986 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (17 / 288)), (2, (-11 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 3)), (8, (1 / 18)), (25, (-1 / 3)), (26, (2 / 9)), (35, (1 / 6)), (54, (-1 / 3)), (97, (1 / 2)), (228, (-1 / 6))]

def value2987 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 96)), (2, (11 / 144)), (3, (11 / 18)), (4, (1 / 6)), (5, (-13 / 72)), (6, (1 / 32)), (7, (1 / 18)), (8, (1 / 18)), (26, (2 / 9)), (35, (2 / 9)), (52, (7 / 18)), (99, (1 / 2))]

def value2988 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (17 / 288)), (2, (7 / 96)), (3, (4 / 9)), (5, (-7 / 36)), (6, (1 / 36)), (7, (2 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (13, (7 / 18)), (35, (5 / 6)), (52, (11 / 18)), (54, (-1 / 6)), (60, (7 / 18)), (69, (1 / 9)), (82, (1 / 18)), (128, (5 / 18)), (260, (-1 / 3)), (392, (1 / 2)), (492, (-1 / 6))]

def value2989 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-29 / 288)), (2, (1 / 9)), (3, (1 / 1)), (4, (1 / 6)), (5, (-1 / 18)), (6, (1 / 288)), (7, (1 / 6)), (8, (1 / 9)), (12, (2 / 9)), (13, (1 / 9)), (26, (2 / 9)), (33, (-5 / 6)), (35, (1 / 18)), (52, (1 / 18)), (54, (-1 / 3)), (81, (-1 / 3)), (100, (1 / 2)), (228, (-1 / 6))]

def value2990 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 48)), (2, (1 / 9)), (3, (7 / 9)), (5, (-1 / 9)), (6, (5 / 288)), (7, (1 / 9)), (12, (2 / 9)), (13, (8 / 9)), (35, (4 / 9)), (52, (5 / 9)), (98, (1 / 2)), (102, (1 / 2))]

def value2991 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (25 / 288)), (2, (25 / 288)), (3, (1 / 2)), (5, (-2 / 9)), (6, (1 / 36)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 9)), (13, (8 / 9)), (35, (2 / 3)), (52, (7 / 9)), (59, (-1 / 3)), (60, (4 / 9)), (82, (1 / 6)), (128, (5 / 9)), (201, (-1 / 6)), (392, (1 / 2)), (399, (1 / 2))]

def value2992 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 288)), (2, (5 / 48)), (3, (7 / 9)), (4, (1 / 6)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (12, (2 / 9)), (13, (2 / 9)), (26, (2 / 9)), (33, (-5 / 6)), (35, (1 / 6)), (52, (1 / 6)), (81, (-1 / 3)), (104, (1 / 2))]

def value2993 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-1 / 32)), (2, (-1 / 36)), (3, (17 / 18)), (4, (1 / 6)), (5, (-1 / 12)), (7, (1 / 2)), (12, (1 / 18)), (23, (-1 / 6)), (25, (-2 / 3)), (26, (7 / 18)), (33, (-1 / 6)), (35, (1 / 6)), (51, (-1 / 6)), (52, (1 / 18)), (54, (-5 / 6)), (64, (-1 / 3)), (69, (1 / 18)), (97, (1 / 1)), (124, (-1 / 6)), (260, (-1 / 6)), (383, (1 / 2))]

def value2994 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-17 / 288)), (2, (1 / 72)), (3, (1 / 2)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (12, (5 / 18)), (23, (-1 / 3)), (25, (-1 / 3)), (26, (2 / 9)), (35, (1 / 18)), (38, (1 / 2)), (43, (1 / 1)), (54, (-1 / 3)), (97, (1 / 1)), (98, (1 / 1))]

def value2995 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 36)), (2, (-1 / 32)), (3, (8 / 9)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 9)), (12, (1 / 6)), (23, (-1 / 6)), (26, (1 / 3)), (35, (1 / 6)), (44, (1 / 1)), (51, (-1 / 3)), (52, (1 / 9)), (54, (-1 / 2)), (99, (1 / 1)), (100, (1 / 1))]

def value2996 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (13 / 72)), (2, (-1 / 96)), (3, (-1 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 9)), (13, (1 / 18)), (25, (-1 / 3)), (26, (2 / 9)), (38, (1 / 2)), (54, (-1 / 6))]

def value2997 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-11 / 96)), (2, (25 / 288)), (3, (2 / 3)), (4, (1 / 6)), (12, (13 / 18)), (13, (2 / 3)), (26, (1 / 18)), (41, (1 / 2))]

def value2998 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-31 / 288)), (2, (1 / 18)), (3, (8 / 9)), (4, (1 / 3)), (5, (-1 / 18)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 18)), (26, (1 / 9)), (31, (-1 / 6)), (35, (1 / 18)), (51, (-2 / 3)), (52, (5 / 18)), (54, (-1 / 6)), (95, (1 / 2))]

def value2999 : Sparse (Fin 909) := [(0, (3 / 80)), (1, (-67 / 288)), (2, (13 / 96)), (3, (5 / 9)), (12, (1 / 6)), (13, (1 / 6)), (31, (-1 / 3)), (33, (-1 / 3))]

def value3000 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-37 / 288)), (2, (17 / 288)), (3, (7 / 6)), (4, (2 / 9)), (12, (7 / 9)), (13, (17 / 18)), (25, (-1 / 6)), (33, (-2 / 3)), (59, (-1 / 2)), (94, (1 / 2)), (101, (1 / 1))]

def value3001 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-59 / 288)), (2, (5 / 36)), (3, (23 / 18)), (4, (4 / 9)), (12, (4 / 9)), (13, (13 / 18)), (31, (-1 / 3)), (33, (-1 / 3)), (42, (1 / 1))]

def value3002 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-61 / 288)), (2, (1 / 12)), (3, (1 / 1)), (4, (1 / 3)), (12, (7 / 18)), (13, (4 / 9)), (25, (-2 / 3)), (26, (2 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (38, (1 / 2)), (39, (1 / 1)), (54, (-1 / 2))]

def value3003 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-53 / 288)), (2, (7 / 72)), (3, (5 / 6)), (4, (7 / 18)), (5, (-1 / 72)), (7, (1 / 9)), (12, (1 / 6)), (13, (1 / 18)), (26, (1 / 6)), (31, (-1 / 6)), (41, (1 / 2)), (46, (1 / 1)), (51, (-1 / 3)), (52, (1 / 18)), (95, (1 / 2)), (103, (1 / 1))]

def value3004 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-13 / 72)), (2, (23 / 288)), (3, (11 / 18)), (4, (11 / 18)), (12, (2 / 9)), (13, (1 / 6)), (26, (7 / 18)), (31, (-1 / 3)), (33, (-1 / 3)), (41, (1 / 2))]

def value3005 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-5 / 96)), (2, (11 / 96)), (3, (11 / 18)), (5, (-5 / 72)), (7, (2 / 9)), (8, (1 / 18)), (12, (2 / 9)), (13, (2 / 9)), (24, (-1 / 6)), (25, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (51, (-1 / 3)), (52, (1 / 6)), (59, (-1 / 6)), (94, (1 / 2)), (95, (1 / 2))]

def value3006 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-11 / 144)), (3, (4 / 9)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 9)), (12, (2 / 9)), (13, (1 / 9)), (23, (-1 / 6)), (25, (-1 / 6)), (26, (2 / 9)), (33, (-1 / 3)), (35, (1 / 9)), (43, (1 / 1)), (51, (-1 / 6)), (52, (1 / 18)), (54, (-1 / 3)), (59, (-1 / 6)), (94, (1 / 2)), (103, (1 / 1)), (104, (1 / 1))]

def value3007 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 32)), (2, (19 / 288)), (3, (1 / 1)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 144)), (7, (7 / 18)), (12, (1 / 9)), (13, (11 / 18)), (26, (1 / 3)), (34, (1 / 6)), (35, (11 / 18)), (52, (7 / 18)), (54, (-1 / 3)), (60, (1 / 6)), (64, (-1 / 6)), (69, (1 / 18)), (99, (1 / 2)), (126, (-1 / 6)), (128, (1 / 18)), (260, (-1 / 6)), (400, (1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3008 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-29 / 144)), (2, (1 / 18)), (3, (13 / 18)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 9)), (13, (1 / 18)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 6)), (35, (1 / 18)), (39, (1 / 2)), (42, (1 / 2)), (44, (1 / 2)), (54, (-1 / 6)), (56, (-1 / 6)), (97, (1 / 2)), (99, (1 / 1)), (100, (1 / 2))]

def value3009 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (5 / 288)), (2, (1 / 16)), (3, (8 / 9)), (4, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (12, (1 / 6)), (13, (7 / 9)), (26, (5 / 18)), (34, (1 / 6)), (35, (4 / 9)), (52, (1 / 3)), (60, (1 / 6)), (98, (1 / 1)), (99, (1 / 2)), (116, (1 / 2)), (128, (1 / 18)), (237, (-1 / 6)), (392, (1 / 2)), (398, (1 / 2))]

def value3010 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (-1 / 32)), (2, (11 / 288)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 8)), (6, (1 / 144)), (12, (1 / 18)), (13, (1 / 3)), (26, (1 / 6)), (34, (1 / 18)), (35, (5 / 18)), (52, (7 / 18)), (54, (-1 / 6)), (60, (1 / 18)), (103, (1 / 1)), (116, (1 / 2)), (392, (1 / 2))]

def value3011 : Sparse (Fin 909) := [(0, (13 / 720)), (1, (-17 / 144)), (2, (-5 / 72)), (3, (5 / 9)), (4, (1 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 9)), (13, (2 / 9)), (25, (-1 / 6)), (26, (1 / 9)), (39, (1 / 2)), (54, (-1 / 6))]

def value3012 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-29 / 144)), (2, (11 / 144)), (3, (5 / 9)), (4, (1 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 18)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (39, (1 / 2)), (54, (-1 / 6))]

def value3013 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-7 / 48)), (2, (1 / 8)), (3, (11 / 18)), (4, (1 / 3)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 6)), (31, (-1 / 3)), (33, (-1 / 3)), (42, (1 / 2))]

def value3014 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-59 / 288)), (2, (1 / 18)), (3, (13 / 18)), (4, (1 / 9)), (12, (7 / 18)), (13, (1 / 2)), (42, (1 / 2))]

def value3015 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (1 / 16)), (2, (5 / 36)), (3, (17 / 18)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 96)), (8, (1 / 9)), (12, (1 / 3)), (13, (19 / 18)), (26, (1 / 18)), (33, (-1 / 6)), (34, (1 / 18)), (35, (1 / 9)), (52, (1 / 2)), (59, (-1 / 3)), (60, (1 / 18)), (102, (1 / 1)), (120, (1 / 2)), (128, (1 / 9)), (399, (1 / 2))]

def value3016 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 144)), (2, (19 / 288)), (3, (10 / 9)), (4, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (12, (7 / 18)), (13, (4 / 3)), (26, (5 / 18)), (33, (-1 / 6)), (34, (2 / 9)), (35, (1 / 2)), (51, (-1 / 6)), (52, (1 / 2)), (59, (-1 / 3)), (60, (2 / 9)), (103, (1 / 2)), (128, (1 / 6)), (398, (1 / 2))]

def value3017 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 8)), (2, (23 / 288)), (3, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (4 / 9)), (13, (11 / 18)), (33, (-1 / 3)), (38, (1 / 2)), (54, (-1 / 6))]

def value3018 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 12)), (2, (1 / 16)), (3, (5 / 6)), (4, (1 / 18)), (12, (4 / 9)), (13, (8 / 9)), (26, (1 / 9)), (33, (-1 / 3)), (41, (1 / 2))]

def value3019 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 144)), (2, (-1 / 48)), (3, (2 / 3)), (5, (-1 / 18)), (6, (1 / 72)), (7, (1 / 2)), (8, (1 / 9)), (25, (-1 / 6)), (26, (1 / 3)), (35, (5 / 6)), (54, (-1 / 3)), (64, (-1 / 3)), (67, (5 / 18)), (199, (-1 / 6)), (228, (-1 / 3)), (271, (-1 / 3)), (425, (1 / 2))]

def value3020 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-5 / 96)), (2, (1 / 24)), (3, (13 / 18)), (4, (1 / 18)), (5, (-1 / 18)), (7, (1 / 6)), (8, (1 / 18)), (12, (7 / 18)), (23, (-2 / 3)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 24)), (43, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 3)), (77, (1 / 2)), (105, (1 / 2))]

def value3021 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (3 / 32)), (3, (1 / 1)), (4, (5 / 18)), (5, (-11 / 72)), (6, (5 / 288)), (7, (4 / 9)), (8, (1 / 6)), (13, (1 / 18)), (26, (11 / 18)), (34, (1 / 9)), (35, (13 / 18)), (52, (7 / 18)), (56, (-1 / 6)), (67, (2 / 9)), (81, (-1 / 3)), (201, (-1 / 6)), (228, (-1 / 3)), (275, (-1 / 3)), (428, (1 / 2)), (460, (1 / 2))]

def value3022 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-13 / 72)), (2, (17 / 288)), (3, (19 / 18)), (4, (5 / 9)), (5, (-5 / 72)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 6)), (26, (1 / 2)), (35, (1 / 9)), (56, (-1 / 3)), (107, (1 / 2)), (228, (-1 / 6))]

def value3023 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 9)), (2, (1 / 18)), (3, (2 / 3)), (4, (1 / 18)), (5, (-1 / 24)), (7, (2 / 9)), (8, (1 / 18)), (12, (7 / 18)), (13, (1 / 18)), (25, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (1 / 18)), (51, (-1 / 3)), (54, (-1 / 6)), (100, (1 / 2)), (105, (1 / 2))]

def value3024 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 288)), (2, (13 / 144)), (3, (2 / 3)), (4, (5 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 18)), (8, (2 / 9)), (26, (5 / 18)), (52, (1 / 18)), (56, (-1 / 3)), (81, (-1 / 3)), (107, (1 / 2)), (228, (-1 / 6))]

def value3025 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-11 / 144)), (2, (7 / 72)), (3, (1 / 3)), (4, (2 / 9)), (5, (-1 / 18)), (7, (1 / 18)), (8, (2 / 9)), (26, (1 / 18)), (31, (-1 / 2)), (51, (-1 / 3)), (56, (-1 / 6)), (106, (1 / 2)), (107, (1 / 2))]

def value3026 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (-71 / 288)), (2, (1 / 8)), (3, (5 / 9)), (4, (1 / 3)), (5, (-1 / 18)), (7, (1 / 18)), (8, (2 / 9)), (12, (1 / 6)), (26, (1 / 18)), (31, (-1 / 6)), (45, (1 / 1)), (51, (-1 / 3)), (56, (-1 / 6)), (105, (1 / 2)), (107, (1 / 2))]

def value3027 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-35 / 144)), (2, (3 / 32)), (3, (1 / 1)), (4, (11 / 18)), (5, (-1 / 24)), (7, (2 / 9)), (8, (1 / 18)), (12, (1 / 9)), (25, (-1 / 3)), (26, (1 / 6)), (31, (-1 / 2)), (35, (1 / 18)), (46, (1 / 1)), (51, (-1 / 3)), (54, (-1 / 6)), (97, (1 / 2)), (106, (1 / 2))]

def value3028 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-7 / 72)), (2, (3 / 32)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 18)), (27, (1 / 24)), (31, (-1 / 6)), (43, (1 / 2)), (46, (1 / 2)), (51, (-1 / 3)), (77, (1 / 2)), (106, (1 / 2)), (122, (1 / 1))]

def value3029 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 24)), (2, (11 / 96)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 6)), (6, (1 / 144)), (7, (7 / 18)), (8, (1 / 3)), (12, (1 / 9)), (13, (2 / 9)), (26, (1 / 9)), (33, (-1 / 3)), (34, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (54, (-1 / 6)), (59, (-1 / 3)), (81, (-2 / 3)), (199, (-1 / 6)), (228, (-1 / 3)), (271, (-1 / 3)), (307, (-1 / 2)), (426, (1 / 2)), (428, (1 / 1))]

def value3030 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 144)), (2, (1 / 32)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (2 / 9)), (23, (-1 / 3)), (25, (-1 / 6)), (27, (1 / 12)), (33, (-1 / 3)), (51, (-1 / 3)), (54, (-1 / 3))]

def value3031 : Sparse (Fin 909) := [(0, (19 / 720)), (1, (-13 / 72)), (2, (17 / 144)), (3, (1 / 9)), (4, (1 / 18)), (5, (-1 / 36)), (8, (1 / 6)), (12, (1 / 18)), (27, (1 / 12)), (30, (-1 / 3)), (31, (-1 / 6)), (45, (1 / 2)), (51, (-1 / 6))]

def value3032 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-59 / 288)), (2, (19 / 288)), (3, (11 / 18)), (4, (1 / 2)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 9)), (24, (-1 / 3)), (26, (1 / 9)), (27, (1 / 12)), (31, (-1 / 3)), (51, (-1 / 3)), (56, (-1 / 3))]

def value3033 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-37 / 144)), (2, (1 / 12)), (3, (8 / 9)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (7 / 18)), (23, (-1 / 3)), (25, (-1 / 1)), (26, (1 / 9)), (27, (1 / 12)), (31, (-2 / 3)), (51, (-1 / 3)), (54, (-1 / 3))]

def value3034 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-35 / 288)), (2, (11 / 96)), (3, (7 / 9)), (5, (-1 / 24)), (7, (1 / 9)), (12, (4 / 9)), (23, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 12)), (31, (-1 / 3)), (33, (-1 / 3)), (54, (-1 / 6))]

def value3035 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-29 / 288)), (2, (17 / 288)), (3, (5 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (8, (1 / 18)), (26, (1 / 9)), (31, (-1 / 3)), (46, (1 / 2)), (51, (-1 / 3)), (56, (-1 / 6))]

def value3036 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-31 / 96)), (2, (25 / 288)), (3, (1 / 1)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 2)), (26, (1 / 9)), (45, (1 / 2)), (51, (-1 / 3)), (56, (-1 / 6))]

def value3037 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-37 / 288)), (2, (23 / 288)), (3, (1 / 3)), (4, (2 / 9)), (5, (-1 / 72)), (8, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3)), (45, (1 / 1)), (51, (-1 / 3)), (54, (-1 / 6))]

def value3038 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-7 / 96)), (2, (13 / 288)), (3, (2 / 3)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (12, (5 / 18)), (23, (-5 / 6)), (24, (-2 / 3)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 18)), (55, (-1 / 6)), (79, (1 / 2)), (113, (1 / 2))]

def value3039 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (5 / 36)), (2, (5 / 96)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (12, (2 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8))]

def value3040 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-11 / 36)), (2, (17 / 144)), (3, (2 / 3)), (4, (5 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 3)), (26, (1 / 9)), (27, (1 / 8)), (31, (-2 / 3))]

def value3041 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-59 / 288)), (2, (1 / 12)), (3, (2 / 3)), (4, (5 / 18)), (5, (-1 / 36)), (7, (1 / 9)), (12, (4 / 9)), (23, (-1 / 3)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 12)), (31, (-1 / 6)), (43, (1 / 2)), (55, (-1 / 6))]

def value3042 : Sparse (Fin 909) := [(0, (1 / 45)), (1, (-5 / 16)), (2, (5 / 144)), (3, (7 / 9)), (4, (7 / 9)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 3)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 3)), (44, (1 / 1)), (55, (-1 / 3))]

def value3043 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-1 / 6)), (2, (1 / 36)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 3)), (31, (-2 / 3))]

def value3044 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-11 / 72)), (2, (5 / 72)), (3, (2 / 9)), (4, (1 / 3)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 6)), (31, (-1 / 3))]

def value3045 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-7 / 24)), (2, (1 / 16)), (3, (19 / 18)), (4, (4 / 9)), (12, (2 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (5 / 18)), (27, (1 / 24)), (31, (-1 / 6)), (43, (1 / 2)), (55, (-1 / 3))]

def value3046 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-19 / 72)), (2, (1 / 8)), (3, (2 / 9)), (12, (2 / 9)), (23, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 3))]

def value3047 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-3 / 16)), (2, (1 / 24)), (3, (29 / 18)), (4, (1 / 2)), (5, (-1 / 36)), (7, (5 / 9)), (12, (1 / 6)), (13, (2 / 9)), (24, (-1 / 6)), (26, (17 / 18)), (33, (-1 / 6)), (34, (2 / 9)), (35, (2 / 3)), (67, (2 / 9)), (81, (-1 / 3)), (95, (1 / 2)), (453, (1 / 2))]

def value3048 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-17 / 96)), (2, (1 / 144)), (3, (11 / 18)), (4, (1 / 3)), (7, (1 / 18)), (12, (7 / 18)), (13, (1 / 18)), (23, (-1 / 3)), (25, (-1 / 2)), (26, (1 / 9)), (35, (1 / 18)), (43, (1 / 1)), (50, (1 / 2)), (55, (-1 / 3)), (104, (1 / 1)), (113, (1 / 2))]

def value3049 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-17 / 96)), (2, (1 / 48)), (3, (13 / 18)), (4, (2 / 9)), (7, (1 / 9)), (12, (4 / 9)), (13, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 6)), (26, (1 / 9)), (33, (-1 / 3)), (35, (1 / 9)), (43, (1 / 2)), (50, (1 / 2)), (55, (-1 / 3)), (81, (-1 / 6)), (95, (1 / 2)), (104, (1 / 2)), (113, (1 / 1)), (122, (1 / 2))]

def value3050 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 24)), (2, (19 / 288)), (3, (5 / 6)), (4, (1 / 9)), (5, (-1 / 36)), (7, (5 / 18)), (8, (1 / 18)), (12, (1 / 6)), (13, (2 / 9)), (26, (1 / 3)), (33, (-2 / 3)), (34, (1 / 9)), (35, (1 / 3)), (51, (-1 / 6)), (64, (-1 / 6)), (67, (1 / 9)), (81, (-1 / 3)), (95, (1 / 2)), (104, (1 / 1)), (110, (1 / 2)), (307, (-1 / 6)), (425, (1 / 2)), (472, (1 / 2))]

def value3051 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-79 / 288)), (2, (1 / 96)), (3, (7 / 9)), (4, (5 / 9)), (7, (1 / 18)), (12, (1 / 3)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (35, (1 / 18)), (43, (1 / 2)), (44, (1 / 1)), (55, (-1 / 3)), (95, (1 / 1)), (113, (1 / 2))]

def value3052 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-7 / 288)), (2, (25 / 288)), (3, (23 / 18)), (4, (1 / 3)), (5, (-5 / 36)), (6, (5 / 288)), (7, (4 / 9)), (26, (7 / 9)), (35, (7 / 6)), (52, (5 / 9)), (67, (4 / 9)), (81, (-1 / 3)), (460, (1 / 1))]

def value3053 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-29 / 144)), (2, (19 / 288)), (3, (4 / 9)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 3)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 2)), (35, (1 / 18)), (43, (1 / 1)), (52, (1 / 18)), (95, (1 / 2)), (113, (1 / 2))]

def value3054 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (13 / 288)), (2, (7 / 72)), (3, (13 / 18)), (4, (1 / 9)), (5, (-11 / 72)), (6, (1 / 96)), (7, (1 / 3)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 3)), (33, (-2 / 3)), (35, (5 / 9)), (52, (2 / 9)), (59, (-2 / 3)), (67, (2 / 9)), (81, (-1 / 3)), (201, (-1 / 6)), (307, (-1 / 2)), (425, (1 / 2)), (428, (1 / 1))]

def value3055 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-11 / 144)), (2, (1 / 144)), (3, (17 / 18)), (4, (7 / 18)), (5, (-1 / 72)), (7, (1 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (11 / 18)), (34, (1 / 6)), (35, (1 / 3)), (44, (1 / 2)), (52, (1 / 9)), (67, (1 / 6)), (99, (1 / 2)), (119, (1 / 2)), (453, (1 / 2)), (460, (1 / 2))]

def value3056 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-13 / 288)), (2, (-1 / 144)), (3, (17 / 18)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 9)), (12, (1 / 6)), (25, (-2 / 3)), (26, (1 / 3)), (33, (-1 / 3)), (54, (-1 / 6)), (64, (-1 / 3))]

def value3057 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-17 / 288)), (2, (1 / 48)), (3, (1 / 2)), (4, (5 / 18)), (12, (4 / 9)), (25, (-1 / 3)), (26, (1 / 9)), (43, (1 / 2))]

def value3058 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-17 / 96)), (2, (1 / 18)), (3, (8 / 9)), (4, (2 / 9)), (12, (11 / 18)), (13, (7 / 18)), (25, (-1 / 6)), (26, (1 / 18)), (33, (-1 / 3)), (34, (1 / 18)), (43, (1 / 1)), (116, (1 / 2))]

def value3059 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 16)), (2, (17 / 288)), (3, (1 / 1)), (4, (5 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (26, (5 / 9)), (31, (-1 / 6)), (33, (-1 / 6)), (34, (1 / 18)), (35, (1 / 6)), (52, (2 / 9)), (67, (1 / 18)), (81, (-1 / 3)), (119, (1 / 2)), (460, (1 / 2))]

def value3060 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-19 / 96)), (2, (1 / 36)), (3, (2 / 3)), (4, (4 / 9)), (12, (1 / 18)), (26, (2 / 9)), (31, (-1 / 3)), (44, (1 / 2))]

def value3061 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-1 / 9)), (2, (13 / 288)), (3, (5 / 6)), (4, (1 / 3)), (12, (2 / 3)), (13, (1 / 9)), (25, (-1 / 6)), (33, (-1 / 3))]

def value3062 : Sparse (Fin 909) := [(0, (13 / 288)), (1, (-67 / 288)), (2, (13 / 144)), (3, (7 / 18)), (4, (5 / 18)), (12, (1 / 18)), (31, (-1 / 2)), (45, (1 / 2))]

def value3063 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-3 / 16)), (2, (23 / 288)), (3, (8 / 9)), (4, (5 / 9)), (12, (1 / 6)), (13, (1 / 18)), (26, (1 / 6)), (31, (-1 / 2)), (33, (-1 / 2)), (34, (1 / 18)), (42, (1 / 2)), (119, (1 / 2))]

def value3064 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-7 / 72)), (2, (19 / 288)), (3, (8 / 9)), (4, (4 / 9)), (12, (1 / 6)), (13, (5 / 18)), (26, (5 / 18)), (31, (-1 / 6)), (34, (1 / 6)), (42, (1 / 2)), (44, (1 / 2)), (45, (1 / 2)), (119, (1 / 2)), (120, (1 / 2))]

def value3065 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 96)), (2, (13 / 288)), (3, (13 / 18)), (4, (2 / 9)), (12, (2 / 9)), (13, (2 / 9)), (25, (-1 / 2)), (26, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 6)), (34, (1 / 9)), (39, (1 / 2)), (43, (1 / 2)), (46, (1 / 2)), (54, (-1 / 6)), (64, (-1 / 6)), (112, (1 / 2)), (116, (1 / 2))]

def value3066 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-5 / 32)), (2, (5 / 72)), (3, (13 / 18)), (4, (5 / 18)), (12, (5 / 18)), (25, (-2 / 3)), (26, (1 / 18)), (31, (-1 / 2)), (33, (-2 / 3)), (39, (1 / 2)), (54, (-1 / 6)), (64, (-1 / 6)), (112, (1 / 2))]

def value3067 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-59 / 288)), (2, (17 / 288)), (3, (2 / 3)), (4, (1 / 2)), (12, (2 / 9)), (25, (-1 / 3)), (26, (1 / 9)), (31, (-1 / 2)), (46, (1 / 2))]

def value3068 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-29 / 288)), (2, (1 / 12)), (3, (5 / 9)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 18)), (12, (2 / 9)), (13, (1 / 18)), (25, (-1 / 3)), (31, (-1 / 3)), (33, (-1 / 2)), (46, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (81, (-1 / 6)), (122, (1 / 2))]

def value3069 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-5 / 32)), (2, (11 / 288)), (3, (1 / 2)), (4, (1 / 3)), (12, (2 / 9)), (13, (1 / 18)), (25, (-1 / 3)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (43, (1 / 2))]

def value3070 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 48)), (2, (11 / 96)), (3, (11 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 6)), (33, (-5 / 6)), (52, (1 / 9)), (59, (-1 / 6)), (64, (-1 / 6)), (81, (-1 / 3)), (112, (1 / 2)), (307, (-1 / 6)), (428, (1 / 2))]

def value3071 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 36)), (2, (1 / 48)), (3, (2 / 3)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (25, (-1 / 6)), (26, (1 / 3)), (33, (-1 / 2)), (34, (1 / 9)), (35, (2 / 9)), (43, (1 / 2)), (52, (1 / 18)), (59, (-1 / 6)), (64, (-1 / 6)), (67, (1 / 9)), (103, (1 / 2)), (112, (1 / 2)), (307, (-1 / 6)), (428, (1 / 2)), (472, (1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1856 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-1 / 32)), (2, (-13 / 48)), (3, (-1 / 1)), (5, (1 / 4)), (7, (-2 / 3)), (8, (-2 / 3)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 6)), (51, (1 / 1)), (59, (1 / 2))]

def value1857 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 12)), (2, (-1 / 32)), (3, (-1 / 3)), (7, (-1 / 3)), (23, (1 / 1)), (24, (1 / 2)), (27, (-1 / 8)), (51, (1 / 2)), (54, (1 / 2)), (55, (1 / 2)), (64, (1 / 2)), (124, (1 / 1)), (125, (3 / 2)), (126, (1 / 1)), (196, (1 / 2)), (197, (1 / 2)), (266, (1 / 2))]

def value1858 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 96)), (3, (-1 / 3)), (5, (1 / 6)), (6, (-5 / 96)), (26, (-1 / 3)), (35, (-1 / 3)), (52, (-1 / 3)), (123, (1 / 2))]

def value1859 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (5 / 96)), (2, (-7 / 96)), (3, (-5 / 6)), (5, (1 / 8)), (7, (-1 / 2)), (8, (-1 / 6)), (13, (-1 / 6)), (26, (-1 / 2)), (34, (-1 / 6)), (35, (-1 / 2)), (51, (1 / 2)), (54, (1 / 2)), (64, (1 / 2)), (67, (-1 / 6))]

def value1860 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (3 / 32)), (2, (-1 / 8)), (3, (-7 / 6)), (4, (-1 / 3)), (5, (1 / 24)), (7, (-1 / 3)), (12, (-1 / 3)), (13, (-5 / 6)), (26, (-2 / 3)), (34, (-1 / 3)), (35, (-2 / 3)), (52, (-1 / 3)), (67, (-1 / 6))]

def value1861 : Sparse (Fin 909) := [(0, (1 / 120)), (3, (-2 / 3)), (5, (1 / 6)), (6, (-1 / 24)), (13, (-2 / 3)), (35, (-1 / 3)), (52, (-2 / 3))]

def value1862 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 48)), (2, (-7 / 96)), (3, (-1 / 1)), (4, (-1 / 6)), (12, (-1 / 3)), (13, (-1 / 1)), (26, (-1 / 6)), (33, (2 / 1)), (34, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 6)), (60, (-1 / 6)), (61, (1 / 2)), (127, (1 / 2)), (128, (-1 / 6)), (489, (2 / 1))]

def value1863 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (5 / 96)), (2, (-7 / 32)), (3, (-5 / 3)), (5, (1 / 24)), (7, (-1 / 6)), (12, (-2 / 3)), (13, (-7 / 6)), (34, (-1 / 6)), (35, (-1 / 6)), (51, (1 / 1)), (52, (-1 / 2)), (54, (1 / 2)), (64, (1 / 2))]

def value1864 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (11 / 96)), (2, (1 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (7, (-1 / 6)), (12, (-1 / 6)), (23, (1 / 2)), (25, (1 / 2)), (26, (-1 / 3)), (35, (-1 / 6)), (51, (1 / 2)), (54, (1 / 2)), (55, (1 / 2)), (64, (1 / 2)), (123, (1 / 2)), (124, (1 / 2)), (125, (1 / 2)), (259, (1 / 2)), (266, (1 / 2)), (487, (-1 / 1))]

def value1865 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 24)), (2, (1 / 32)), (3, (-1 / 1)), (4, (-1 / 3)), (5, (1 / 24)), (7, (-1 / 3)), (25, (1 / 2)), (26, (-2 / 3)), (34, (-1 / 6)), (35, (-1 / 2)), (52, (-1 / 6)), (64, (1 / 2)), (67, (-1 / 6)), (123, (1 / 2))]

def value1866 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 32)), (2, (-1 / 32)), (3, (-3 / 2)), (4, (-1 / 2)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (26, (-5 / 6)), (33, (1 / 2)), (34, (-1 / 3)), (35, (-1 / 3)), (67, (-1 / 6)), (81, (1 / 2))]

def value1867 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-5 / 96)), (2, (-5 / 96)), (3, (-2 / 3)), (5, (1 / 6)), (6, (-1 / 32)), (13, (-1 / 3)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 6)), (52, (-2 / 3)), (123, (1 / 1)), (237, (1 / 1)), (306, (1 / 2)), (489, (1 / 1))]

def value1868 : Sparse (Fin 909) := [(1, (1 / 6)), (2, (-1 / 12)), (3, (-7 / 6)), (4, (-1 / 3)), (12, (-1 / 3)), (13, (-1 / 3)), (25, (1 / 2)), (26, (-1 / 3)), (31, (1 / 1)), (33, (1 / 1)), (34, (-1 / 6)), (51, (1 / 1)), (52, (-1 / 6)), (64, (1 / 2)), (123, (1 / 1))]

def value1869 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 12)), (2, (1 / 32)), (3, (-1 / 2)), (5, (5 / 24)), (6, (-1 / 48)), (11, (-1 / 3)), (13, (-1 / 1)), (26, (-1 / 3)), (34, (-1 / 3)), (35, (-4 / 3)), (52, (-2 / 3)), (60, (-2 / 3)), (82, (-1 / 6)), (128, (-1 / 3)), (276, (-1 / 3)), (490, (1 / 1))]

def value1870 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 96)), (2, (-19 / 96)), (3, (-5 / 6)), (5, (3 / 8)), (6, (-1 / 48)), (7, (-2 / 3)), (9, (1 / 24)), (26, (-1 / 6)), (27, (-1 / 8)), (35, (-1 / 3)), (52, (-2 / 3)), (68, (-1 / 8)), (69, (-1 / 2)), (124, (1 / 2)), (126, (1 / 1)), (493, (1 / 2)), (495, (-1 / 6))]

def value1871 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 12)), (2, (-5 / 32)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (1 / 8)), (7, (-1 / 3)), (8, (-1 / 3)), (24, (1 / 1)), (27, (-1 / 8)), (51, (1 / 2)), (52, (-1 / 6)), (69, (-1 / 6)), (124, (1 / 2)), (126, (2 / 1))]

def value1872 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 96)), (2, (-5 / 96)), (3, (-1 / 3)), (5, (5 / 24)), (6, (-1 / 32)), (7, (-1 / 6)), (9, (1 / 24)), (13, (-2 / 3)), (35, (-1 / 3)), (52, (-2 / 3)), (54, (1 / 2)), (68, (-1 / 8)), (69, (-1 / 3)), (125, (1 / 1)), (126, (1 / 2)), (128, (-1 / 6)), (492, (1 / 2)), (494, (1 / 2)), (495, (-1 / 6))]

def value1873 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-19 / 96)), (2, (-1 / 48)), (3, (-1 / 3)), (5, (-1 / 6)), (7, (-2 / 3)), (9, (1 / 24)), (69, (-1 / 3)), (124, (1 / 2))]

def value1874 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 96)), (2, (1 / 96)), (3, (-1 / 6)), (5, (1 / 12)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 2)), (35, (-1 / 3)), (69, (-1 / 6)), (70, (-1 / 6)), (124, (1 / 2)), (125, (1 / 2))]

def value1875 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 96)), (2, (-3 / 32)), (3, (-1 / 3)), (5, (1 / 4)), (6, (-1 / 32)), (7, (-1 / 6)), (9, (1 / 8)), (35, (-1 / 3)), (52, (-1 / 3)), (58, (-1 / 96)), (69, (-1 / 3)), (310, (-1 / 3)), (495, (-1 / 3))]

def value1876 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (-5 / 48)), (3, (-1 / 3)), (5, (1 / 6)), (6, (-1 / 32)), (7, (-1 / 6)), (8, (-1 / 3)), (9, (1 / 24)), (52, (-1 / 3)), (69, (-1 / 6)), (71, (-1 / 6)), (126, (1 / 2))]

def value1877 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 24)), (2, (-25 / 96)), (3, (-1 / 2)), (5, (7 / 24)), (7, (-2 / 3)), (8, (-2 / 3)), (27, (-1 / 8)), (51, (1 / 1)), (69, (-1 / 6)), (71, (-1 / 6)), (124, (1 / 2)), (126, (1 / 2))]

def value1878 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 12)), (2, (-1 / 12)), (3, (-2 / 3)), (5, (1 / 3)), (6, (-1 / 16)), (7, (-1 / 3)), (9, (1 / 24)), (13, (-5 / 6)), (35, (-2 / 3)), (52, (-2 / 3)), (69, (-1 / 6)), (70, (-1 / 6)), (125, (1 / 2))]

def value1879 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 8)), (2, (-7 / 48)), (3, (-1 / 6)), (5, (5 / 12)), (6, (-1 / 24)), (9, (1 / 12)), (13, (-2 / 3)), (35, (-1 / 3)), (52, (-1 / 1)), (58, (-1 / 96)), (69, (-1 / 6)), (82, (-2 / 3)), (128, (-5 / 6)), (278, (-1 / 6)), (310, (-1 / 3)), (492, (1 / 2)), (495, (-1 / 3))]

def value1880 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 6)), (2, (1 / 48)), (5, (1 / 24)), (7, (-1 / 2)), (12, (-1 / 2)), (13, (-1 / 3)), (35, (-1 / 3))]

def value1881 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 8)), (2, (-1 / 96)), (3, (-1 / 2)), (7, (-1 / 6)), (10, (1 / 2)), (12, (-1 / 3)), (13, (-2 / 3)), (35, (-1 / 3)), (82, (-1 / 6)), (127, (1 / 2)), (128, (-1 / 6))]

def value1882 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 96)), (2, (-1 / 16)), (3, (-1 / 6)), (4, (-1 / 6)), (5, (1 / 8)), (6, (-1 / 48)), (26, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 6)), (308, (1 / 2)), (310, (-1 / 6)), (493, (1 / 2)), (495, (-1 / 6))]

def value1883 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (1 / 48)), (2, (-5 / 48)), (3, (-1 / 2)), (4, (-1 / 6)), (5, (1 / 6)), (6, (-1 / 96)), (7, (-1 / 6)), (8, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 6))]

def value1884 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 12)), (2, (-7 / 48)), (3, (-1 / 3)), (5, (1 / 8)), (7, (-1 / 6)), (8, (-1 / 3))]

def value1885 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (-13 / 96)), (3, (-2 / 3)), (5, (1 / 8)), (6, (-1 / 96)), (7, (-1 / 3)), (8, (-1 / 6)), (12, (-1 / 3)), (13, (-1 / 3)), (35, (-1 / 6)), (51, (1 / 2)), (52, (-1 / 6))]

def value1886 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 96)), (2, (-5 / 96)), (3, (-1 / 2)), (5, (1 / 6)), (6, (-1 / 24)), (12, (-1 / 6)), (13, (-5 / 6)), (35, (-1 / 3)), (51, (1 / 2)), (52, (-1 / 2)), (82, (-1 / 6)), (128, (-1 / 3)), (309, (1 / 2)), (310, (-1 / 6)), (494, (1 / 2)), (495, (-1 / 6))]

def value1887 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 12)), (2, (-5 / 48)), (3, (-2 / 3)), (5, (5 / 24)), (6, (-1 / 48)), (12, (-1 / 6)), (13, (-1 / 1)), (35, (-1 / 3)), (52, (-2 / 3)), (82, (-1 / 6)), (128, (-1 / 3))]

def value1888 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (1 / 4)), (2, (-1 / 48)), (3, (-2 / 1)), (12, (-2 / 1)), (13, (-8 / 3)), (127, (3 / 2)), (128, (-1 / 2))]

def value1889 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (1 / 96)), (2, (-7 / 96)), (3, (-7 / 6)), (4, (-1 / 2)), (26, (-1 / 2)), (35, (-1 / 2)), (51, (3 / 2)), (52, (-1 / 2)), (55, (3 / 2)), (493, (3 / 2)), (494, (1 / 1)), (495, (-1 / 6))]

def value1890 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 4)), (2, (-5 / 24)), (3, (-3 / 2)), (4, (-1 / 2)), (12, (-1 / 2)), (13, (-1 / 3)), (51, (3 / 2)), (52, (-1 / 2))]

def value1891 : Sparse (Fin 909) := [(0, (-11 / 240)), (1, (7 / 16)), (2, (-5 / 24)), (3, (-1 / 1)), (12, (-1 / 2)), (13, (-1 / 3))]

def value1892 : Sparse (Fin 909) := [(36, (-1 / 2)), (72, (-1 / 2)), (316, (-1 / 2)), (498, (-1 / 2))]

def value1893 : Sparse (Fin 909) := [(38, (-1 / 2)), (72, (-1 / 2)), (318, (-1 / 2)), (499, (-1 / 2))]

def value1894 : Sparse (Fin 909) := [(39, (-1 / 2)), (74, (-1 / 2)), (319, (-1 / 2)), (500, (-1 / 2))]

def value1895 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (5, (1 / 36)), (7, (1 / 18)), (8, (-1 / 18)), (72, (-1 / 2)), (287, (-1 / 2)), (425, (-1 / 2))]

def value1896 : Sparse (Fin 909) := [(3, (-1 / 9)), (7, (-1 / 9)), (35, (-1 / 9)), (81, (1 / 6)), (104, (-1 / 2)), (425, (-1 / 2)), (499, (-1 / 2))]

def value1897 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 96)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 9)), (81, (1 / 6)), (100, (-1 / 2)), (426, (-1 / 2)), (500, (-1 / 2))]

def value1898 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (33, (1 / 6)), (54, (1 / 6)), (330, (-1 / 2)), (426, (-1 / 2)), (498, (-1 / 2))]

def value1899 : Sparse (Fin 909) := [(12, (-1 / 18)), (13, (-1 / 9)), (59, (1 / 6)), (72, (-1 / 2)), (74, (-1 / 2)), (199, (1 / 6)), (426, (-1 / 2))]

def value1900 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 72)), (7, (1 / 18)), (35, (-1 / 18)), (83, (-1 / 2)), (316, (-1 / 2)), (501, (-1 / 2))]

def value1901 : Sparse (Fin 909) := [(3, (-1 / 9)), (7, (-1 / 9)), (35, (-1 / 9)), (73, (-1 / 2)), (81, (1 / 6)), (84, (-1 / 2)), (318, (-1 / 2))]

def value1902 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 6)), (8, (-1 / 6)), (35, (-1 / 18)), (81, (1 / 6)), (85, (-1 / 2)), (319, (-1 / 2))]

def value1903 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (-1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (10, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 6)), (228, (1 / 6)), (501, (-1 / 2)), (727, (1 / 6))]

def value1904 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 36)), (10, (1 / 6)), (35, (-1 / 18)), (69, (-1 / 18)), (308, (1 / 6))]

def value1905 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-5 / 96)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 9)), (8, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 18)), (81, (1 / 6)), (238, (1 / 6)), (307, (1 / 6))]

def value1906 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 72)), (5, (1 / 36)), (8, (1 / 18)), (85, (-1 / 2)), (330, (-1 / 2)), (508, (-1 / 2))]

def value1907 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (-1 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (-1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (81, (1 / 6)), (228, (1 / 6)), (307, (1 / 6)), (508, (-1 / 2)), (727, (1 / 6))]

def value1908 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-7 / 288)), (3, (-1 / 6)), (5, (5 / 72)), (6, (-1 / 288)), (7, (-1 / 3)), (8, (-1 / 6)), (10, (1 / 3)), (13, (-1 / 18)), (35, (-2 / 9)), (81, (1 / 6)), (82, (-1 / 18)), (307, (1 / 6))]

def value1909 : Sparse (Fin 909) := [(37, (-1 / 2)), (73, (-1 / 2)), (501, (-1 / 2)), (503, (-1 / 2))]

def value1910 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-2 / 9)), (8, (-1 / 18)), (35, (-1 / 6)), (73, (-1 / 2)), (81, (1 / 6)), (322, (-1 / 2))]

def value1911 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-2 / 9)), (8, (-1 / 6)), (35, (-1 / 18)), (81, (1 / 6)), (107, (-1 / 2)), (428, (-1 / 2))]

def value1912 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 288)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 18)), (81, (1 / 2)), (326, (-1 / 2))]

def value1913 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 9)), (26, (-1 / 18)), (81, (1 / 3)), (228, (1 / 6)), (330, (-1 / 2)), (501, (-1 / 2))]

def value1914 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 9)), (4, (-1 / 9)), (26, (-1 / 18)), (56, (1 / 6)), (428, (-1 / 2)), (501, (-1 / 2)), (508, (-1 / 2))]

def value1915 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (73, (-1 / 2)), (75, (-1 / 2)), (201, (1 / 6)), (428, (-1 / 2))]

def value1916 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (1 / 48)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 9)), (26, (-2 / 9)), (35, (-2 / 9)), (67, (-1 / 6)), (238, (1 / 6)), (307, (1 / 6))]

def value1917 : Sparse (Fin 909) := [(1, (1 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-5 / 18)), (67, (-1 / 9)), (307, (1 / 6)), (503, (-1 / 2)), (727, (1 / 6))]

def value1918 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 6)), (10, (1 / 3)), (12, (-1 / 6)), (13, (-1 / 9)), (55, (1 / 3)), (59, (1 / 6)), (321, (-1 / 2)), (727, (1 / 6))]

def value1919 : Sparse (Fin 909) := [(38, (-1 / 2)), (72, (-1 / 2)), (321, (-1 / 2)), (505, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1920 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (-1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 18)), (9, (1 / 72)), (10, (1 / 3)), (27, (-1 / 12)), (55, (1 / 6)), (68, (-1 / 24)), (308, (1 / 6)), (727, (1 / 6))]

def value1921 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 3)), (59, (1 / 3)), (259, (1 / 6)), (308, (1 / 6))]

def value1922 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 6)), (54, (1 / 3)), (59, (1 / 6)), (82, (-1 / 18)), (199, (1 / 3)), (259, (1 / 6)), (723, (1 / 6))]

def value1923 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 18)), (31, (1 / 6)), (33, (1 / 6)), (35, (-1 / 18)), (51, (1 / 6)), (59, (1 / 6)), (238, (1 / 6)), (307, (1 / 6)), (326, (-1 / 2))]

def value1924 : Sparse (Fin 909) := [(42, (-1 / 2)), (76, (-1 / 2)), (326, (-1 / 2)), (506, (-1 / 2))]

def value1925 : Sparse (Fin 909) := [(39, (-1 / 2)), (74, (-1 / 2)), (330, (-1 / 2)), (507, (-1 / 2))]

def value1926 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (33, (1 / 6)), (35, (-1 / 18)), (55, (1 / 6)), (59, (1 / 6)), (307, (1 / 6)), (330, (-1 / 2)), (727, (1 / 6))]

def value1927 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 9)), (8, (-1 / 18)), (10, (1 / 6)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 6)), (55, (1 / 6)), (508, (-1 / 2)), (727, (1 / 6))]

def value1928 : Sparse (Fin 909) := [(40, (-1 / 2)), (75, (-1 / 2)), (508, (-1 / 1))]

def value1929 : Sparse (Fin 909) := [(3, (-1 / 6)), (10, (1 / 3)), (12, (-1 / 6)), (13, (-5 / 18)), (33, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (59, (1 / 2)), (82, (-1 / 18)), (128, (-1 / 18)), (307, (1 / 6))]

def value1930 : Sparse (Fin 909) := [(2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (8, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (59, (1 / 6)), (69, (-1 / 18)), (124, (1 / 6)), (259, (1 / 6)), (321, (-1 / 2))]

def value1931 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (10, (1 / 6)), (35, (-1 / 18)), (72, (-1 / 2)), (74, (-1 / 2)), (282, (-1 / 2))]

def value1932 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-2 / 9)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (228, (1 / 6)), (321, (-1 / 2)), (508, (-1 / 2))]

def value1933 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 36)), (5, (1 / 18)), (6, (-1 / 72)), (11, (-1 / 9)), (26, (-1 / 9)), (505, (-1 / 2)), (727, (1 / 6))]

def value1934 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 18)), (8, (-1 / 18)), (9, (1 / 72)), (26, (-1 / 18)), (35, (-1 / 9)), (68, (-1 / 24)), (238, (1 / 6)), (307, (1 / 3)), (309, (1 / 6)), (727, (1 / 6))]

def value1935 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 48)), (6, (-1 / 144)), (9, (1 / 36)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 6)), (68, (-1 / 24)), (727, (1 / 6))]

def value1936 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 288)), (2, (-1 / 32)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 18)), (71, (-1 / 9)), (236, (1 / 6)), (508, (-1 / 2))]

def value1937 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 144)), (2, (-5 / 96)), (3, (-1 / 18)), (5, (5 / 36)), (6, (-1 / 144)), (7, (-5 / 18)), (8, (-1 / 6)), (10, (1 / 6)), (35, (-1 / 18)), (71, (-1 / 18)), (308, (1 / 6))]

def value1938 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 36)), (5, (1 / 9)), (6, (-1 / 48)), (7, (-1 / 9)), (8, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 18)), (59, (1 / 6)), (71, (-1 / 18)), (259, (1 / 6))]

def value1939 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (5 / 144)), (5, (-5 / 72)), (6, (7 / 144)), (9, (1 / 72)), (35, (-1 / 9)), (82, (-1 / 9)), (199, (1 / 6)), (723, (1 / 6))]

def value1940 : Sparse (Fin 909) := [(2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 144)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 6)), (228, (1 / 3)), (517, (-1 / 2))]

def value1941 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 144)), (35, (-1 / 9)), (52, (-1 / 18)), (228, (1 / 6))]

def value1942 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-5 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (26, (-1 / 18)), (107, (-1 / 2)), (112, (-1 / 2))]

def value1943 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 144)), (2, (-1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (33, (1 / 3)), (51, (1 / 6)), (55, (1 / 6)), (137, (-1 / 2)), (145, (-1 / 2))]

def value1944 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 36)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 6)), (112, (-1 / 2)), (137, (-1 / 2)), (146, (-1 / 2))]

def value1945 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 9)), (7, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (64, (1 / 2)), (125, (1 / 6)), (238, (1 / 6)), (543, (-1 / 2))]

def value1946 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 144)), (2, (-1 / 96)), (3, (-2 / 9)), (13, (-1 / 9)), (26, (-2 / 9)), (34, (-1 / 6)), (35, (-1 / 18)), (64, (1 / 6)), (238, (1 / 6))]

def value1947 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (-1 / 144)), (3, (-1 / 6)), (13, (-2 / 9)), (26, (-1 / 18)), (34, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (204, (-1 / 2)), (472, (-1 / 2))]

def value1948 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (-7 / 288)), (3, (-1 / 3)), (12, (-1 / 18)), (13, (-1 / 6)), (26, (-1 / 18)), (34, (-1 / 6)), (51, (1 / 6)), (52, (-1 / 9)), (64, (1 / 6))]

def value1949 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (-5 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (13, (-1 / 6)), (26, (-1 / 18)), (34, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 18)), (64, (1 / 6)), (125, (1 / 6)), (138, (-1 / 2))]

def value1950 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 6)), (139, (-1 / 2)), (472, (-1 / 2)), (546, (-1 / 2))]

def value1951 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (34, (-1 / 9)), (35, (-1 / 18)), (55, (1 / 6)), (64, (1 / 6)), (139, (-1 / 2))]

def value1952 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-2 / 9)), (35, (-1 / 18)), (52, (-1 / 18)), (54, (1 / 6)), (59, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (199, (1 / 6)), (540, (-1 / 2)), (721, (1 / 6)), (723, (1 / 6))]

def value1953 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (-1 / 72)), (6, (-1 / 288)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (56, (1 / 6)), (201, (1 / 6)), (228, (1 / 6)), (541, (-1 / 2)), (796, (1 / 6))]

def value1954 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (27, (-1 / 24)), (52, (-1 / 18)), (55, (1 / 6)), (69, (-1 / 18)), (125, (1 / 6)), (126, (1 / 6)), (538, (-1 / 2))]

def value1955 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (47, (-1 / 2)), (51, (1 / 6)), (538, (-1 / 2)), (539, (-1 / 2))]

def value1956 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 96)), (2, (-1 / 96)), (5, (1 / 18)), (23, (1 / 6)), (27, (-1 / 8)), (55, (1 / 3)), (68, (-1 / 24)), (125, (1 / 6))]

def value1957 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-5 / 288)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (23, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (55, (1 / 6)), (125, (1 / 6)), (146, (-1 / 2))]

def value1958 : Sparse (Fin 909) := [(17, (-1 / 2)), (40, (-1 / 2)), (146, (-1 / 1))]

def value1959 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (7, (-1 / 18)), (51, (1 / 6)), (124, (1 / 6)), (140, (-1 / 2)), (205, (-1 / 2)), (539, (-1 / 2))]

def value1960 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 36)), (2, (-1 / 48)), (3, (-1 / 9)), (7, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 3)), (124, (1 / 6)), (140, (-1 / 2))]

def value1961 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (1 / 18)), (42, (-1 / 2)), (97, (-1 / 2)), (110, (-1 / 2))]

def value1962 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (47, (-1 / 2)), (51, (1 / 6)), (110, (-1 / 2)), (143, (-1 / 2))]

def value1963 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (12, (-1 / 9)), (23, (1 / 6)), (110, (-1 / 2)), (140, (-1 / 2)), (144, (-1 / 2))]

def value1964 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (-1 / 144)), (3, (-2 / 9)), (12, (-1 / 6)), (13, (-1 / 9)), (51, (1 / 6)), (55, (1 / 6)), (140, (-1 / 2)), (146, (-1 / 2))]

def value1965 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (38, (-1 / 2)), (39, (-1 / 2)), (54, (1 / 6)), (110, (-1 / 2))]

def value1966 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 9)), (54, (1 / 3)), (141, (-1 / 2)), (196, (1 / 6))]

def value1967 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (125, (1 / 6)), (141, (-1 / 2))]

def value1968 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 32)), (2, (-5 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 9)), (64, (1 / 6)), (69, (-1 / 18)), (125, (1 / 6)), (126, (1 / 6)), (543, (-1 / 2))]

def value1969 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 72)), (2, (-19 / 288)), (3, (-1 / 9)), (5, (5 / 72)), (6, (-1 / 288)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 6)), (69, (-1 / 9)), (125, (1 / 6)), (126, (1 / 6))]

def value1970 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 288)), (2, (-1 / 36)), (3, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (126, (1 / 3)), (146, (-1 / 2)), (208, (-1 / 2))]

def value1971 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 72)), (3, (-1 / 18)), (8, (-1 / 18)), (31, (1 / 6)), (51, (2 / 3)), (52, (-1 / 18)), (126, (1 / 6)), (238, (1 / 6)), (538, (-1 / 2))]

def value1972 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-17 / 288)), (2, (-5 / 96)), (3, (-2 / 9)), (5, (1 / 72)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-2 / 9)), (126, (1 / 6)), (237, (1 / 6)), (539, (-1 / 2))]

def value1973 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-13 / 288)), (5, (5 / 72)), (6, (-1 / 72)), (13, (-1 / 18)), (52, (1 / 6)), (69, (-1 / 18)), (128, (-1 / 18)), (540, (-1 / 2))]

def value1974 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 72)), (35, (-1 / 18)), (52, (-1 / 9)), (228, (1 / 3)), (540, (-1 / 2)), (728, (1 / 6))]

def value1975 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (2, (1 / 36)), (3, (-1 / 18)), (5, (1 / 36)), (13, (-1 / 18)), (56, (1 / 3)), (144, (-1 / 2)), (197, (1 / 6))]

def value1976 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 72)), (2, (-7 / 288)), (8, (-1 / 9)), (33, (1 / 6)), (51, (1 / 3)), (126, (1 / 6)), (145, (-1 / 2))]

def value1977 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (-1 / 24)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 18)), (64, (1 / 3)), (68, (-1 / 24)), (125, (1 / 6)), (238, (1 / 3))]

def value1978 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (13 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 96)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 9)), (68, (-1 / 24)), (125, (1 / 6))]

def value1979 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-5 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (8, (-1 / 9)), (146, (-1 / 2)), (236, (1 / 6))]

def value1980 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 288)), (13, (-1 / 18)), (26, (-1 / 18)), (27, (-1 / 24)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (55, (1 / 6)), (64, (1 / 3)), (238, (1 / 6))]

def value1981 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-7 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 96)), (13, (-1 / 18)), (52, (-1 / 18)), (237, (1 / 6)), (546, (-1 / 2))]

def value1982 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 96)), (2, (-5 / 144)), (3, (-2 / 9)), (12, (-1 / 9)), (13, (-1 / 9)), (33, (1 / 6)), (51, (1 / 3)), (52, (-1 / 18)), (142, (-1 / 2))]

def value1983 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (8, (-1 / 18)), (51, (1 / 2)), (52, (-1 / 18)), (95, (-1 / 2)), (738, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1984 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (1 / 72)), (3, (-1 / 6)), (12, (-1 / 18)), (13, (-5 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6)), (56, (1 / 6)), (143, (-1 / 2))]

def value1985 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (2, (-1 / 24)), (3, (-1 / 9)), (5, (1 / 72)), (13, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 6)), (102, (-1 / 2)), (739, (-1 / 2))]

def value1986 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 18)), (11, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 6)), (59, (1 / 6)), (128, (-1 / 18)), (228, (1 / 6)), (545, (-1 / 2)), (721, (1 / 6))]

def value1987 : Sparse (Fin 909) := [(1, (-5 / 96)), (2, (-7 / 144)), (5, (1 / 9)), (6, (-7 / 288)), (8, (-1 / 18)), (13, (-1 / 9)), (52, (-1 / 6)), (59, (1 / 6)), (128, (-1 / 9)), (721, (1 / 6))]

def value1988 : Sparse (Fin 909) := [(12, (-1 / 18)), (13, (-1 / 9)), (59, (1 / 6)), (72, (-1 / 2)), (199, (1 / 6)), (284, (-1 / 2)), (499, (-1 / 2))]

def value1989 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (59, (1 / 6)), (73, (-1 / 2)), (284, (-1 / 2)), (502, (-1 / 2))]

def value1990 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 144)), (2, (-1 / 96)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 9)), (24, (1 / 3)), (37, (-1 / 2)), (99, (-1 / 2))]

def value1991 : Sparse (Fin 909) := [(3, (-1 / 18)), (4, (-1 / 18)), (26, (-1 / 18)), (81, (1 / 6)), (83, (-1 / 2)), (84, (-1 / 2)), (228, (1 / 6)), (317, (-1 / 2))]

def value1992 : Sparse (Fin 909) := [(3, (1 / 18)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (84, (-1 / 2)), (317, (-1 / 2)), (709, (-1 / 2))]

def value1993 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 9)), (7, (-1 / 18)), (26, (-1 / 6)), (37, (-1 / 2))]

def value1994 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 6)), (44, (-1 / 2)), (48, (-1 / 2))]

def value1995 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (21, (-1 / 2)), (37, (-1 / 2)), (48, (-1 / 2))]

def value1996 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 288)), (3, (-1 / 18)), (4, (1 / 18)), (18, (-1 / 2)), (37, (-1 / 2)), (47, (-1 / 2))]

def value1997 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 96)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (15, (-1 / 2)), (36, (-1 / 2)), (48, (-1 / 2))]

def value1998 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 36)), (2, (-1 / 72)), (14, (-1 / 2)), (23, (1 / 3)), (25, (1 / 3))]

def value1999 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 288)), (2, (-1 / 288)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 6)), (15, (-1 / 2)), (23, (1 / 6)), (25, (1 / 6))]

def value2000 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-1 / 144)), (17, (-1 / 2)), (23, (1 / 6)), (25, (1 / 3)), (31, (1 / 6))]

def value2001 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (1 / 12)), (3, (-2 / 9)), (16, (-1 / 2)), (23, (1 / 6))]

def value2002 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (15, (-1 / 2)), (18, (-1 / 2)), (25, (1 / 6)), (38, (-1 / 2))]

def value2003 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 8)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-2 / 9)), (17, (-1 / 2)), (23, (1 / 6))]

def value2004 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 18)), (12, (1 / 18)), (16, (-1 / 2)), (38, (-1 / 2)), (50, (-1 / 2))]

def value2005 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (59, (1 / 2)), (199, (1 / 6)), (502, (-1 / 2))]

def value2006 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (59, (1 / 3)), (201, (1 / 6)), (287, (-1 / 2)), (499, (-1 / 2))]

def value2007 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (37, (-1 / 2)), (56, (1 / 6))]

def value2008 : Sparse (Fin 909) := [(23, (1 / 6)), (55, (1 / 6)), (125, (1 / 6)), (140, (-1 / 2)), (145, (-1 / 2)), (383, (-1 / 2))]

def value2009 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (1 / 96)), (3, (-1 / 6)), (12, (-1 / 9)), (13, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (55, (1 / 3)), (139, (-1 / 2)), (398, (-1 / 2))]

def value2010 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (13, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (60, (-1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (324, (-1 / 2))]

def value2011 : Sparse (Fin 909) := [(1, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (52, (-1 / 9)), (60, (-1 / 9)), (70, (-1 / 18)), (125, (1 / 6)), (128, (-1 / 18)), (260, (1 / 6)), (323, (-1 / 2))]

def value2012 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (138, (-1 / 2)), (146, (-1 / 2)), (197, (1 / 6)), (400, (-1 / 2))]

def value2013 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (15, (-1 / 2)), (24, (1 / 6))]

def value2014 : Sparse (Fin 909) := [(0, (-1 / 360)), (2, (-1 / 72)), (17, (-1 / 2)), (30, (1 / 6))]

def value2015 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (7 / 96)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (18, (-1 / 2))]

def value2016 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 48)), (3, (1 / 9)), (4, (-1 / 9)), (26, (-1 / 9))]

def value2017 : Sparse (Fin 909) := [(1, (-5 / 144)), (2, (-1 / 144)), (25, (1 / 6)), (31, (1 / 3))]

def value2018 : Sparse (Fin 909) := [(0, (-17 / 1440)), (1, (29 / 288)), (3, (-2 / 9)), (4, (-2 / 9)), (12, (-1 / 9)), (25, (1 / 6)), (31, (1 / 6))]

def value2019 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 24)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 6)), (13, (-1 / 18)), (55, (1 / 6)), (119, (-1 / 2)), (177, (-1 / 2))]

def value2020 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 288)), (3, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (34, (-1 / 6)), (35, (-1 / 18)), (139, (-1 / 2))]

def value2021 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 48)), (3, (-1 / 3)), (4, (-1 / 9)), (12, (-1 / 6)), (25, (1 / 6))]

def value2022 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-1 / 96)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 9)), (31, (1 / 6)), (33, (1 / 2)), (55, (1 / 6)), (177, (-1 / 2))]

def value2023 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (13 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (12, (-1 / 9)), (18, (-1 / 2)), (25, (1 / 6))]

def value2024 : Sparse (Fin 909) := [(1, (5 / 288)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (35, (-1 / 18)), (69, (-1 / 18)), (70, (-1 / 18)), (124, (1 / 6)), (125, (1 / 6)), (126, (1 / 6)), (197, (1 / 6)), (291, (-1 / 2))]

def value2025 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (7, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (79, (-1 / 2)), (640, (-1 / 2)), (751, (-1 / 2))]

def value2026 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (5, (1 / 72)), (7, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6)), (72, (-1 / 2)), (199, (1 / 6)), (498, (-1 / 2)), (505, (-1 / 2))]

def value2027 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 72)), (7, (1 / 18)), (35, (-1 / 18)), (73, (-1 / 2)), (501, (-1 / 2)), (503, (-1 / 2))]

def value2028 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6)), (97, (-1 / 2)), (100, (-1 / 2)), (300, (-1 / 2))]

def value2029 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (1 / 18)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (104, (-1 / 2)), (291, (-1 / 2)), (300, (-1 / 2))]

def value2030 : Sparse (Fin 909) := [(38, (-1 / 2)), (313, (-1 / 2)), (505, (-1 / 2)), (540, (-1 / 2))]

def value2031 : Sparse (Fin 909) := [(37, (-1 / 2)), (84, (-1 / 2)), (503, (-1 / 2)), (541, (-1 / 2))]

def value2032 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (23, (1 / 6)), (27, (-1 / 24)), (68, (-1 / 24)), (125, (1 / 2)), (126, (1 / 3))]

def value2033 : Sparse (Fin 909) := [(3, (-1 / 9)), (10, (1 / 6)), (12, (-1 / 9)), (13, (-2 / 9)), (33, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (59, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (306, (1 / 6)), (313, (-1 / 2)), (721, (1 / 6))]

def value2034 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 9)), (7, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 9)), (55, (1 / 3)), (70, (-1 / 18)), (125, (1 / 6)), (197, (1 / 6)), (640, (-1 / 2))]

def value2035 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 288)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 9)), (23, (1 / 3)), (24, (1 / 3)), (27, (-1 / 24)), (55, (1 / 6)), (125, (1 / 6)), (126, (1 / 6))]

def value2036 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (12, (-1 / 9)), (23, (1 / 6)), (47, (-1 / 2)), (140, (-1 / 2)), (205, (-1 / 2))]

def value2037 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (7 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 9)), (54, (1 / 6)), (56, (1 / 6)), (70, (-1 / 18)), (125, (1 / 6)), (197, (1 / 6)), (643, (-1 / 2))]

def value2038 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 36)), (5, (1 / 18)), (6, (-1 / 72)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (1 / 6)), (70, (-1 / 18)), (82, (-1 / 18)), (505, (-1 / 2))]

def value2039 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-1 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (35, (-1 / 6)), (52, (-1 / 9)), (84, (-1 / 2)), (323, (-1 / 2)), (541, (-1 / 2))]

def value2040 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 36)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 6)), (48, (-1 / 2)), (137, (-1 / 2)), (207, (-1 / 2))]

def value2041 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 36)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (12, (-1 / 18)), (51, (1 / 6)), (54, (1 / 6)), (100, (-1 / 2)), (125, (1 / 6)), (126, (1 / 6))]

def value2042 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 288)), (2, (-1 / 18)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 9)), (13, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (125, (1 / 6)), (126, (1 / 6))]

def value2043 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 96)), (2, (-1 / 36)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6)), (56, (1 / 6)), (100, (-1 / 2))]

def value2044 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (31, (1 / 6)), (47, (-1 / 2)), (48, (-1 / 2)), (51, (1 / 6)), (177, (-1 / 2))]

def value2045 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (35, (-1 / 18)), (52, (-1 / 9)), (84, (-1 / 2)), (228, (1 / 6)), (313, (-1 / 2)), (324, (-1 / 2))]

def value2046 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 32)), (3, (-5 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-5 / 18)), (52, (-1 / 3)), (201, (1 / 6)), (313, (-1 / 2))]

def value2047 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 6)), (5, (1 / 36)), (7, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (81, (1 / 3)), (306, (1 / 6)), (499, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2112 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 48)), (2, (-1 / 32)), (3, (-2 / 3)), (7, (-1 / 3)), (12, (-1 / 3)), (23, (1 / 1)), (25, (1 / 2)), (54, (1 / 1)), (124, (1 / 2)), (125, (1 / 1)), (196, (1 / 2))]

def value2113 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-5 / 96)), (3, (-2 / 3)), (5, (5 / 24)), (6, (-1 / 24)), (7, (-1 / 2)), (9, (1 / 12)), (11, (-1 / 6)), (26, (-1 / 6)), (35, (-5 / 6)), (52, (-1 / 2)), (69, (-1 / 3)), (70, (-1 / 3)), (228, (1 / 2)), (278, (-1 / 6)), (495, (-1 / 6)), (726, (1 / 2))]

def value2114 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 48)), (2, (-1 / 16)), (3, (-5 / 6)), (4, (-1 / 6)), (5, (1 / 8)), (6, (-1 / 96)), (7, (-1 / 2)), (24, (1 / 2)), (26, (-1 / 3)), (35, (-1 / 2)), (52, (-1 / 6)), (69, (-1 / 6)), (70, (-1 / 6)), (126, (1 / 2)), (197, (1 / 2))]

def value2115 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 8)), (2, (-5 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 3)), (12, (-1 / 6)), (23, (1 / 1)), (24, (1 / 1)), (27, (-1 / 4)), (51, (1 / 2)), (55, (1 / 1)), (124, (1 / 2)), (125, (1 / 2)), (126, (1 / 2)), (197, (1 / 2))]

def value2116 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (-1 / 48)), (3, (-2 / 3)), (5, (1 / 6)), (6, (-1 / 48)), (7, (-1 / 2)), (12, (-1 / 6)), (13, (-2 / 3)), (23, (1 / 2)), (35, (-2 / 3)), (52, (-1 / 3)), (54, (1 / 1)), (69, (-1 / 6)), (70, (-1 / 6)), (125, (1 / 2)), (196, (1 / 2))]

def value2117 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 48)), (3, (-1 / 6)), (6, (-1 / 96)), (7, (-1 / 3)), (9, (1 / 12)), (13, (-1 / 6)), (35, (-2 / 3)), (52, (-1 / 6)), (54, (1 / 2)), (69, (-1 / 6)), (70, (-1 / 6)), (82, (-1 / 3)), (128, (-1 / 6)), (199, (1 / 1)), (201, (1 / 2)), (278, (-1 / 6)), (492, (1 / 2)), (495, (-1 / 6)), (723, (1 / 2)), (726, (1 / 2))]

def value2118 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 8)), (2, (-1 / 32)), (3, (-7 / 6)), (7, (-1 / 6)), (12, (-1 / 1)), (23, (3 / 2)), (25, (3 / 2)), (54, (1 / 1))]

def value2119 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (29 / 96)), (2, (-1 / 8)), (3, (-3 / 2)), (4, (-2 / 3)), (5, (1 / 24)), (7, (-1 / 2)), (12, (-1 / 6)), (23, (1 / 2)), (24, (1 / 1)), (26, (-1 / 3)), (27, (-1 / 8)), (35, (-1 / 6)), (55, (1 / 2))]

def value2120 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (1 / 3)), (2, (-1 / 12)), (3, (-4 / 3)), (4, (-2 / 3)), (7, (-1 / 2)), (12, (-1 / 3)), (23, (1 / 2)), (24, (1 / 1))]

def value2121 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (13 / 96)), (2, (-1 / 24)), (3, (-7 / 6)), (4, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 3)), (12, (-1 / 2)), (13, (-1 / 6)), (23, (1 / 1)), (24, (1 / 2)), (25, (1 / 2)), (26, (-1 / 6)), (27, (-1 / 8)), (35, (-1 / 6)), (54, (1 / 2)), (55, (1 / 2))]

def value2122 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (11 / 96)), (2, (7 / 96)), (3, (-5 / 6)), (5, (1 / 12)), (6, (-1 / 48)), (7, (-1 / 2)), (12, (-1 / 6)), (13, (-5 / 6)), (26, (-1 / 3)), (35, (-5 / 6)), (54, (3 / 2)), (82, (-1 / 6)), (199, (1 / 2))]

def value2123 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 16)), (2, (-7 / 48)), (3, (-1 / 2)), (5, (3 / 8)), (6, (-1 / 16)), (7, (-1 / 2)), (9, (1 / 4)), (35, (-1 / 1)), (52, (-1 / 1)), (58, (-1 / 96)), (69, (-1 / 2)), (70, (-1 / 3)), (278, (-1 / 2)), (310, (-1 / 2)), (495, (-1 / 1)), (726, (3 / 2))]

def value2124 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 96)), (2, (-25 / 96)), (3, (-1 / 1)), (5, (1 / 2)), (6, (-1 / 16)), (7, (-1 / 1)), (9, (1 / 24)), (35, (-1 / 1)), (52, (-1 / 1)), (69, (-1 / 2)), (70, (-1 / 3))]

def value2125 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 24)), (2, (1 / 24)), (3, (-2 / 3)), (5, (1 / 24)), (7, (-1 / 3)), (12, (-1 / 3)), (23, (1 / 2))]

def value2126 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (-1 / 48)), (3, (-1 / 3)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 2)), (23, (1 / 2)), (25, (1 / 2)), (35, (-1 / 6)), (54, (1 / 2))]

def value2127 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (-1 / 16)), (3, (-1 / 6)), (4, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-1 / 6)), (11, (-1 / 6)), (26, (-1 / 3)), (35, (-1 / 3)), (52, (-1 / 6)), (228, (1 / 2)), (278, (-1 / 6)), (310, (-1 / 6)), (495, (-1 / 3)), (726, (1 / 2))]

def value2128 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 24)), (2, (-3 / 32)), (3, (-1 / 2)), (4, (-1 / 3)), (5, (1 / 8)), (6, (-1 / 96)), (7, (-1 / 3)), (26, (-1 / 3)), (35, (-1 / 3)), (52, (-1 / 3))]

def value2129 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (1 / 48)), (2, (-3 / 32)), (3, (-1 / 2)), (4, (-1 / 3)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 6)), (24, (1 / 2))]

def value2130 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (11 / 48)), (2, (-1 / 8)), (3, (-1 / 1)), (4, (-1 / 3)), (5, (1 / 24)), (7, (-1 / 6)), (8, (-1 / 6)), (12, (-1 / 2)), (23, (1 / 2)), (24, (1 / 2)), (27, (-1 / 8)), (51, (1 / 1)), (55, (1 / 1))]

def value2131 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 3)), (2, (-1 / 6)), (3, (-4 / 3)), (5, (1 / 24)), (7, (-1 / 3)), (12, (-5 / 6)), (23, (1 / 2))]

def value2132 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (11 / 96)), (2, (-1 / 24)), (3, (-4 / 3)), (5, (1 / 12)), (6, (-1 / 96)), (7, (-1 / 6)), (12, (-2 / 3)), (13, (-3 / 2)), (35, (-1 / 2)), (52, (-1 / 3)), (54, (1 / 2))]

def value2133 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 12)), (2, (-1 / 8)), (3, (-1 / 2)), (5, (5 / 24)), (6, (-5 / 96)), (12, (-1 / 6)), (13, (-1 / 1)), (35, (-2 / 3)), (52, (-2 / 3)), (82, (-2 / 3)), (128, (-2 / 3)), (199, (1 / 2)), (201, (1 / 1)), (278, (-1 / 6)), (310, (-1 / 6)), (495, (-1 / 3)), (726, (1 / 2))]

def value2134 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (2, (-3 / 16)), (3, (-2 / 3)), (5, (7 / 24)), (6, (-1 / 16)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 1)), (35, (-2 / 3)), (52, (-2 / 3)), (82, (-2 / 3)), (128, (-2 / 3)), (199, (1 / 2)), (201, (1 / 1))]

def value2135 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-1 / 8)), (2, (-1 / 48)), (3, (-1 / 1)), (13, (-2 / 3))]

def value2136 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (5 / 96)), (2, (-5 / 96)), (3, (-1 / 2)), (4, (-1 / 6)), (12, (-1 / 6)), (26, (-1 / 3)), (35, (-1 / 6)), (51, (1 / 2)), (52, (-1 / 6)), (55, (1 / 2))]

def value2137 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (1 / 6)), (2, (-7 / 96)), (3, (-1 / 2)), (4, (-1 / 3)), (12, (-1 / 3))]

def value2138 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (25 / 96)), (2, (-1 / 24)), (3, (-7 / 6)), (4, (-1 / 2)), (12, (-1 / 2)), (13, (-1 / 2)), (26, (-1 / 6)), (35, (-1 / 6)), (51, (1 / 2)), (52, (-1 / 6)), (55, (1 / 2))]

def value2139 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (11 / 32)), (2, (-7 / 96)), (3, (-4 / 3)), (4, (-1 / 3)), (12, (-2 / 3)), (13, (-1 / 2))]

def value2140 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 96)), (2, (-1 / 32)), (3, (-5 / 6)), (4, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 48)), (12, (-1 / 3)), (13, (-1 / 1)), (26, (-1 / 6)), (35, (-1 / 2)), (52, (-1 / 3)), (56, (1 / 2)), (82, (-1 / 6)), (128, (-1 / 6)), (201, (1 / 2))]

def value2141 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (11 / 32)), (2, (1 / 96)), (3, (-2 / 1)), (4, (-1 / 1)), (12, (-1 / 2)), (13, (-1 / 3)), (26, (-1 / 1)), (35, (-1 / 2)), (55, (3 / 2))]

def value2142 : Sparse (Fin 909) := [(0, (-31 / 480)), (1, (11 / 16)), (2, (-5 / 96)), (3, (-3 / 2)), (4, (-1 / 1)), (12, (-1 / 1)), (13, (-1 / 3))]

def value2143 : Sparse (Fin 909) := [(1, (-7 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 6)), (52, (-1 / 18)), (59, (1 / 2)), (199, (1 / 6)), (201, (1 / 6)), (289, (-1 / 2))]

def value2144 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 288)), (5, (1 / 36)), (6, (-1 / 144)), (13, (-1 / 6)), (35, (-2 / 9)), (52, (-1 / 6)), (60, (-1 / 6)), (82, (-1 / 18)), (128, (-1 / 9)), (260, (1 / 6)), (309, (1 / 6))]

def value2145 : Sparse (Fin 909) := [(0, (1 / 720)), (2, (-1 / 48)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 6)), (34, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (400, (-1 / 2)), (810, (-1 / 2))]

def value2146 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (142, (-1 / 2)), (383, (-1 / 2)), (538, (-1 / 2))]

def value2147 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 288)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 18)), (9, (1 / 72)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (68, (-1 / 24)), (70, (-1 / 18)), (125, (1 / 6)), (260, (1 / 3)), (309, (1 / 3))]

def value2148 : Sparse (Fin 909) := [(0, (1 / 1440)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 9)), (35, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 9)), (69, (-1 / 18)), (70, (-1 / 18)), (262, (1 / 6)), (309, (1 / 6)), (327, (-1 / 2))]

def value2149 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (-13 / 288)), (5, (5 / 72)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (52, (-1 / 6)), (69, (-1 / 6)), (71, (-1 / 9)), (126, (1 / 3)), (262, (1 / 6))]

def value2150 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (-5 / 144)), (5, (1 / 12)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (52, (-1 / 18)), (69, (-1 / 9)), (71, (-1 / 9)), (126, (1 / 6)), (236, (1 / 6)), (327, (-1 / 2))]

def value2151 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 36)), (2, (-1 / 32)), (3, (-1 / 18)), (5, (1 / 12)), (6, (-1 / 144)), (8, (-1 / 18)), (52, (-1 / 6)), (69, (-1 / 18)), (71, (-1 / 18)), (262, (1 / 6)), (308, (1 / 6)), (322, (-1 / 2))]

def value2152 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (1 / 48)), (5, (1 / 18)), (6, (-5 / 288)), (7, (-1 / 9)), (9, (1 / 36)), (35, (-2 / 9)), (68, (-1 / 24)), (70, (-1 / 6)), (197, (1 / 6)), (309, (1 / 6))]

def value2153 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 288)), (2, (-1 / 36)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (9, (1 / 72)), (27, (-1 / 12)), (51, (1 / 3)), (68, (-1 / 24)), (69, (-1 / 18)), (124, (1 / 6)), (259, (1 / 3)), (308, (1 / 3))]

def value2154 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (51, (1 / 3)), (54, (1 / 3)), (259, (1 / 3)), (282, (-1 / 2)), (308, (1 / 6)), (723, (1 / 6))]

def value2155 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 9)), (23, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6)), (69, (-1 / 18)), (70, (-1 / 18)), (124, (1 / 6)), (196, (1 / 6)), (259, (1 / 6)), (282, (-1 / 2)), (723, (1 / 6))]

def value2156 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-1 / 36)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 144)), (8, (-1 / 18)), (9, (1 / 72)), (27, (-1 / 24)), (51, (1 / 6)), (52, (-1 / 18)), (68, (-1 / 24)), (71, (-1 / 18)), (126, (1 / 6)), (262, (1 / 3)), (308, (1 / 6)), (309, (1 / 6))]

def value2157 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-13 / 288)), (2, (-13 / 288)), (5, (5 / 72)), (6, (-1 / 72)), (8, (-1 / 9)), (51, (1 / 6)), (71, (-1 / 9)), (259, (1 / 6)), (308, (1 / 6)), (325, (-1 / 2))]

def value2158 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (1 / 32)), (5, (1 / 12)), (6, (1 / 144)), (9, (1 / 72)), (54, (1 / 6)), (71, (-1 / 9)), (259, (1 / 3)), (723, (1 / 6))]

def value2159 : Sparse (Fin 909) := [(2, (-1 / 144)), (5, (-1 / 36)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 9)), (69, (-1 / 18)), (71, (-1 / 9)), (282, (-1 / 2)), (308, (1 / 6))]

def value2160 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-5 / 144)), (5, (1 / 24)), (6, (1 / 48)), (9, (1 / 24)), (35, (-1 / 9)), (68, (-1 / 24)), (70, (-1 / 9)), (196, (1 / 6)), (723, (1 / 6))]

def value2161 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 72)), (8, (-1 / 18)), (31, (1 / 6)), (51, (1 / 6)), (107, (-1 / 2)), (238, (1 / 6))]

def value2162 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 144)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (97, (-1 / 2)), (238, (1 / 6))]

def value2163 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 9)), (56, (1 / 6)), (69, (-1 / 18)), (262, (1 / 6)), (735, (-1 / 2))]

def value2164 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 288)), (2, (-1 / 36)), (3, (-1 / 9)), (7, (-1 / 18)), (8, (-1 / 18)), (51, (1 / 3)), (107, (-1 / 2)), (327, (-1 / 2))]

def value2165 : Sparse (Fin 909) := [(1, (5 / 72)), (2, (-1 / 36)), (3, (-1 / 3)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-2 / 9)), (24, (1 / 3)), (26, (-1 / 18)), (35, (-1 / 18)), (126, (1 / 6)), (197, (1 / 6))]

def value2166 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 72)), (2, (-1 / 96)), (3, (-1 / 9)), (7, (-1 / 18)), (46, (-1 / 2)), (51, (1 / 6)), (735, (-1 / 2)), (736, (-1 / 2))]

def value2167 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (-1 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (7, (-1 / 18)), (26, (-1 / 9)), (31, (1 / 6)), (35, (-1 / 18)), (51, (1 / 6)), (107, (-1 / 2)), (238, (1 / 6))]

def value2168 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-5 / 288)), (2, (-1 / 18)), (3, (-1 / 6)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 9)), (51, (1 / 6)), (126, (1 / 3))]

def value2169 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 288)), (2, (-13 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 18)), (8, (-1 / 9)), (107, (-1 / 2)), (126, (1 / 6)), (236, (1 / 6))]

def value2170 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 288)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 9)), (51, (1 / 6)), (106, (-1 / 2)), (735, (-1 / 2))]

def value2171 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-5 / 288)), (2, (-5 / 144)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 6)), (24, (1 / 6)), (30, (1 / 6)), (107, (-1 / 2))]

def value2172 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (-5 / 288)), (3, (-1 / 18)), (31, (1 / 6)), (95, (-1 / 2)), (735, (-1 / 2)), (738, (-1 / 2))]

def value2173 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 144)), (2, (-1 / 36)), (3, (-1 / 6)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (51, (1 / 3)), (52, (-1 / 18)), (95, (-1 / 2))]

def value2174 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (1 / 288)), (3, (-1 / 6)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 6)), (51, (1 / 6)), (70, (-1 / 18)), (238, (1 / 6)), (309, (1 / 6)), (736, (-1 / 2))]

def value2175 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (1 / 48)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (26, (-1 / 6)), (35, (-1 / 9)), (68, (-1 / 24)), (197, (1 / 6)), (238, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2176 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 96)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (55, (1 / 6)), (237, (1 / 6)), (736, (-1 / 2))]

def value2177 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (13, (-1 / 18)), (26, (-1 / 6)), (27, (-1 / 24)), (35, (-1 / 6)), (55, (1 / 6)), (238, (1 / 6))]

def value2178 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 72)), (2, (-1 / 48)), (5, (1 / 36)), (6, (-1 / 288)), (9, (1 / 72)), (27, (-1 / 24)), (51, (1 / 6)), (68, (-1 / 12)), (308, (1 / 6))]

def value2179 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 9)), (4, (-1 / 9)), (26, (-1 / 18)), (51, (1 / 6)), (228, (1 / 6)), (262, (1 / 6)), (796, (1 / 6))]

def value2180 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (31, (1 / 6)), (56, (1 / 6)), (238, (1 / 6)), (262, (1 / 6)), (309, (1 / 6))]

def value2181 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (51, (1 / 6)), (56, (1 / 6)), (77, (-1 / 2)), (97, (-1 / 2)), (286, (-1 / 2))]

def value2182 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (1 / 32)), (5, (1 / 12)), (9, (1 / 72)), (52, (-1 / 9)), (54, (1 / 6)), (721, (1 / 3)), (723, (1 / 6))]

def value2183 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 144)), (2, (-7 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (7, (-1 / 18)), (27, (-1 / 6)), (51, (1 / 3)), (68, (-1 / 24)), (124, (1 / 6))]

def value2184 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 18)), (12, (-1 / 9)), (33, (1 / 3)), (51, (1 / 6)), (54, (1 / 3)), (293, (-1 / 2)), (721, (1 / 6))]

def value2185 : Sparse (Fin 909) := [(1, (1 / 36)), (3, (-1 / 9)), (4, (-1 / 6)), (31, (1 / 3)), (51, (1 / 3)), (56, (1 / 6)), (97, (-1 / 2)), (238, (1 / 6))]

def value2186 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (11 / 288)), (2, (1 / 288)), (3, (-2 / 9)), (7, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 18)), (23, (1 / 3)), (35, (-1 / 18)), (51, (1 / 6)), (54, (1 / 3)), (124, (1 / 6)), (196, (1 / 6))]

def value2187 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (1 / 144)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (25, (1 / 6)), (33, (1 / 6)), (35, (-1 / 18)), (54, (1 / 6)), (63, (1 / 6)), (293, (-1 / 2)), (721, (1 / 6))]

def value2188 : Sparse (Fin 909) := [(43, (-1 / 2)), (77, (-1 / 2)), (97, (-1 / 2)), (737, (-1 / 2))]

def value2189 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (-13 / 288)), (5, (1 / 24)), (8, (-1 / 18)), (27, (-1 / 12)), (31, (1 / 6)), (51, (1 / 3)), (68, (-1 / 24)), (126, (1 / 6)), (238, (1 / 6))]

def value2190 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (7 / 288)), (2, (-1 / 32)), (5, (5 / 72)), (6, (-1 / 144)), (8, (-1 / 18)), (27, (-1 / 12)), (68, (-1 / 24)), (236, (1 / 6))]

def value2191 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 18)), (5, (1 / 36)), (8, (-2 / 9)), (30, (1 / 3)), (236, (1 / 3))]

def value2192 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 96)), (2, (-1 / 24)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (27, (-1 / 12)), (31, (1 / 6)), (51, (1 / 2)), (52, (-1 / 18)), (238, (1 / 6))]

def value2193 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 32)), (2, (1 / 288)), (3, (-5 / 18)), (4, (-1 / 6)), (12, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 2)), (52, (-1 / 18)), (54, (1 / 6)), (56, (1 / 3))]

def value2194 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 288)), (2, (-5 / 288)), (8, (-1 / 18)), (45, (-1 / 2)), (51, (1 / 6)), (738, (-1 / 2)), (739, (-1 / 2))]

def value2195 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 72)), (33, (1 / 6)), (52, (-1 / 18)), (54, (1 / 6)), (721, (1 / 6)), (739, (-1 / 2))]

def value2196 : Sparse (Fin 909) := [(0, (1 / 720)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (51, (1 / 6)), (56, (1 / 6)), (97, (-1 / 2)), (124, (1 / 6)), (197, (1 / 6))]

def value2197 : Sparse (Fin 909) := [(0, (7 / 1440)), (2, (-5 / 288)), (3, (-1 / 9)), (5, (1 / 24)), (7, (-1 / 9)), (8, (-1 / 9)), (51, (1 / 6)), (124, (1 / 6)), (236, (1 / 6))]

def value2198 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (7 / 288)), (2, (1 / 288)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 9)), (8, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (54, (1 / 6)), (56, (1 / 6)), (97, (-1 / 2))]

def value2199 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 144)), (2, (-7 / 288)), (5, (1 / 18)), (7, (-1 / 18)), (8, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 6)), (293, (-1 / 2)), (738, (-1 / 2))]

def value2200 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-13 / 288)), (5, (1 / 24)), (6, (-1 / 72)), (13, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (68, (-1 / 24)), (196, (1 / 6))]

def value2201 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 288)), (5, (1 / 18)), (6, (-7 / 288)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (63, (1 / 6)), (237, (1 / 6)), (721, (1 / 6))]

def value2202 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-11 / 288)), (2, (-1 / 24)), (5, (7 / 72)), (6, (-1 / 144)), (7, (-1 / 6)), (8, (-1 / 6)), (35, (-1 / 9)), (52, (-1 / 9)), (69, (-1 / 18)), (81, (1 / 6)), (306, (1 / 6)), (308, (1 / 6))]

def value2203 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-5 / 144)), (5, (5 / 72)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (81, (1 / 6)), (306, (1 / 6)), (500, (-1 / 2))]

def value2204 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (5 / 144)), (2, (-5 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (8, (-1 / 18)), (24, (1 / 6)), (207, (-1 / 2)), (208, (-1 / 2))]

def value2205 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 3)), (124, (1 / 6)), (745, (-1 / 2)), (753, (-1 / 2))]

def value2206 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 18)), (26, (-1 / 18)), (46, (-1 / 2)), (735, (-1 / 2)), (745, (-1 / 2))]

def value2207 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 18)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (31, (1 / 3)), (49, (-1 / 2)), (107, (-1 / 2))]

def value2208 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (22, (-1 / 2)), (31, (1 / 6)), (46, (-1 / 2)), (204, (-1 / 2))]

def value2209 : Sparse (Fin 909) := [(1, (1 / 36)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (31, (1 / 6)), (35, (-1 / 18)), (51, (1 / 6)), (204, (-1 / 2)), (238, (1 / 6))]

def value2210 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-5 / 144)), (3, (-1 / 6)), (5, (1 / 72)), (8, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (126, (1 / 6)), (146, (-1 / 2))]

def value2211 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 144)), (2, (-11 / 288)), (3, (-5 / 18)), (12, (-1 / 9)), (13, (-1 / 18)), (52, (-1 / 18)), (55, (1 / 6)), (204, (-1 / 2)), (237, (1 / 6))]

def value2212 : Sparse (Fin 909) := [(0, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 6)), (12, (-1 / 18)), (13, (-1 / 6)), (31, (1 / 6)), (33, (1 / 6)), (204, (-1 / 2))]

def value2213 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 288)), (2, (-1 / 36)), (3, (-5 / 18)), (12, (-1 / 9)), (13, (-2 / 9)), (33, (1 / 6)), (51, (1 / 3)), (52, (-1 / 9))]

def value2214 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (7, (-1 / 9)), (23, (1 / 6)), (24, (1 / 6)), (27, (-1 / 12)), (69, (-1 / 18)), (124, (1 / 6)), (126, (1 / 6)), (751, (-1 / 2))]

def value2215 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (-1 / 288)), (24, (1 / 6)), (27, (-1 / 24)), (126, (1 / 6)), (205, (-1 / 2)), (207, (-1 / 2)), (753, (-1 / 2))]

def value2216 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (7, (-1 / 9)), (8, (-1 / 18)), (51, (1 / 3)), (52, (-1 / 18)), (69, (-1 / 18)), (124, (1 / 6)), (126, (1 / 6)), (538, (-1 / 2))]

def value2217 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (12, (-1 / 18)), (51, (1 / 6)), (209, (-1 / 2)), (751, (-1 / 2)), (753, (-1 / 2))]

def value2218 : Sparse (Fin 909) := [(2, (-1 / 144)), (5, (-1 / 36)), (6, (-1 / 144)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (69, (-1 / 18)), (306, (1 / 6)), (498, (-1 / 2))]

def value2219 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (12, (-1 / 18)), (33, (1 / 3)), (54, (1 / 3)), (306, (1 / 6)), (498, (-1 / 2)), (721, (1 / 3)), (723, (1 / 6))]

def value2220 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 6)), (26, (-1 / 9)), (56, (1 / 3)), (81, (1 / 6)), (228, (1 / 3)), (501, (-1 / 2)), (796, (1 / 6))]

def value2221 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 6)), (4, (-1 / 6)), (26, (-1 / 18)), (31, (1 / 6)), (51, (1 / 3)), (56, (1 / 3)), (262, (1 / 6)), (753, (-1 / 2))]

def value2222 : Sparse (Fin 909) := [(1, (5 / 288)), (2, (-7 / 288)), (5, (1 / 36)), (24, (1 / 6)), (27, (-1 / 24)), (68, (-1 / 24)), (126, (1 / 6))]

def value2223 : Sparse (Fin 909) := [(1, (1 / 36)), (3, (-1 / 9)), (4, (-1 / 6)), (51, (1 / 3)), (238, (1 / 6))]

def value2224 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 72)), (2, (-5 / 288)), (3, (-1 / 6)), (7, (-1 / 18)), (12, (-1 / 9)), (23, (1 / 6)), (27, (-1 / 24)), (51, (1 / 6)), (124, (1 / 6)), (205, (-1 / 2))]

def value2225 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (5 / 288)), (3, (-1 / 18)), (4, (-1 / 9)), (31, (1 / 6)), (43, (-1 / 2)), (47, (-1 / 2)), (97, (-1 / 2))]

def value2226 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-7 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (55, (1 / 6)), (81, (1 / 6)), (228, (1 / 6)), (306, (1 / 6)), (541, (-1 / 2)), (728, (1 / 6))]

def value2227 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 288)), (2, (-5 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (8, (-1 / 18)), (24, (1 / 6)), (27, (-1 / 24)), (31, (1 / 6)), (51, (1 / 6)), (126, (1 / 6)), (207, (-1 / 2))]

def value2228 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 288)), (2, (-1 / 24)), (3, (-1 / 6)), (5, (1 / 24)), (6, (-1 / 144)), (27, (-1 / 24)), (52, (-1 / 9)), (68, (-1 / 24)), (126, (1 / 6)), (237, (1 / 6))]

def value2229 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (5 / 96)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (31, (1 / 6)), (51, (1 / 3)), (52, (-1 / 18)), (209, (-1 / 2))]

def value2230 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (11, (-1 / 18)), (26, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 9)), (52, (-1 / 18)), (81, (1 / 6)), (228, (1 / 6)), (306, (1 / 6)), (517, (-1 / 2)), (721, (1 / 6))]

def value2231 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 24)), (2, (-7 / 144)), (3, (-1 / 18)), (5, (5 / 72)), (6, (-5 / 288)), (33, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 9)), (306, (1 / 6)), (721, (1 / 6)), (760, (-1 / 2))]

def value2232 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (7 / 96)), (2, (-1 / 48)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 3)), (27, (-1 / 12)), (126, (1 / 6)), (205, (-1 / 2))]

def value2233 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (24, (1 / 6)), (33, (1 / 3)), (55, (1 / 3)), (299, (-1 / 2)), (306, (1 / 6))]

def value2234 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (12, (-1 / 9)), (15, (-1 / 2)), (23, (1 / 6)), (144, (-1 / 2)), (205, (-1 / 2))]

def value2235 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (13 / 288)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-1 / 18)), (12, (-2 / 9)), (13, (-1 / 9)), (23, (1 / 6)), (25, (1 / 3)), (33, (1 / 3)), (63, (1 / 6))]

def value2236 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (-1 / 144)), (3, (-1 / 9)), (12, (-1 / 9)), (13, (-1 / 9)), (23, (1 / 6)), (25, (1 / 6)), (33, (1 / 6)), (55, (1 / 6)), (63, (1 / 6)), (299, (-1 / 2)), (306, (1 / 6))]

def value2237 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 24)), (2, (-11 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (24, (1 / 6)), (27, (-1 / 24)), (52, (-1 / 18)), (126, (1 / 6)), (208, (-1 / 2))]

def value2238 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 144)), (2, (-1 / 144)), (20, (-1 / 2)), (30, (1 / 6)), (208, (-1 / 1))]

def value2239 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (21, (-1 / 2)), (191, (-1 / 2)), (209, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3072 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-41 / 288)), (2, (7 / 144)), (3, (11 / 18)), (4, (1 / 9)), (7, (1 / 18)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 3)), (25, (-1 / 2)), (33, (-1 / 3)), (38, (1 / 2)), (43, (1 / 1)), (50, (1 / 2)), (110, (1 / 1))]

def value3073 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 4)), (2, (1 / 32)), (3, (1 / 1)), (4, (2 / 9)), (12, (1 / 2)), (13, (1 / 2)), (25, (-1 / 3)), (33, (-1 / 3)), (34, (1 / 18)), (41, (1 / 2)), (50, (1 / 1)), (114, (1 / 2)), (116, (1 / 2))]

def value3074 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-29 / 96)), (2, (7 / 144)), (3, (31 / 18)), (4, (11 / 18)), (12, (5 / 6)), (13, (8 / 9)), (26, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 2)), (34, (2 / 9)), (115, (1 / 2)), (120, (1 / 2))]

def value3075 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-59 / 288)), (2, (5 / 144)), (3, (1 / 1)), (4, (1 / 6)), (12, (11 / 18)), (13, (5 / 9)), (25, (-1 / 2)), (26, (1 / 18)), (31, (-1 / 6)), (33, (-1 / 2)), (34, (1 / 9)), (38, (1 / 2)), (50, (1 / 1)), (54, (-1 / 6)), (64, (-1 / 6)), (110, (1 / 2)), (115, (1 / 2)), (116, (1 / 2))]

def value3076 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-19 / 72)), (2, (19 / 288)), (3, (1 / 2)), (4, (5 / 9)), (25, (-1 / 3)), (26, (1 / 9)), (31, (-5 / 6)), (44, (1 / 2))]

def value3077 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-85 / 288)), (2, (19 / 288)), (3, (17 / 18)), (4, (4 / 9)), (12, (4 / 9)), (26, (2 / 9)), (43, (1 / 2)), (45, (1 / 2))]

def value3078 : Sparse (Fin 909) := [(0, (53 / 1440)), (1, (-13 / 48)), (2, (23 / 288)), (3, (4 / 9)), (4, (4 / 9)), (12, (1 / 18)), (26, (1 / 18)), (31, (-5 / 6)), (43, (1 / 2))]

def value3079 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-47 / 144)), (2, (7 / 144)), (3, (23 / 18)), (4, (7 / 9)), (12, (1 / 3)), (25, (-1 / 3)), (26, (4 / 9)), (31, (-1 / 6)), (43, (1 / 2)), (44, (1 / 2))]

def value3080 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-1 / 16)), (2, (23 / 288)), (3, (5 / 6)), (4, (1 / 3)), (12, (1 / 18)), (25, (-1 / 6)), (26, (1 / 3)), (31, (-1 / 6)), (34, (1 / 18)), (43, (1 / 2)), (46, (1 / 1)), (116, (1 / 2))]

def value3081 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-19 / 144)), (2, (5 / 48)), (3, (1 / 3)), (4, (2 / 9)), (12, (1 / 9)), (25, (-1 / 3)), (31, (-1 / 3))]

def value3082 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-5 / 16)), (2, (3 / 32)), (3, (5 / 6)), (4, (5 / 9)), (12, (2 / 9)), (26, (1 / 9)), (31, (-1 / 3)), (45, (1 / 2)), (46, (1 / 2))]

def value3083 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (-41 / 144)), (2, (13 / 144)), (3, (5 / 9)), (4, (4 / 9)), (12, (5 / 18)), (31, (-1 / 3))]

def value3084 : Sparse (Fin 909) := [(0, (41 / 1440)), (1, (-47 / 144)), (2, (3 / 32)), (3, (11 / 9)), (4, (11 / 18)), (12, (1 / 2)), (13, (1 / 9)), (25, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (34, (1 / 18)), (44, (1 / 2)), (45, (1 / 1)), (120, (1 / 2))]

def value3085 : Sparse (Fin 909) := [(0, (23 / 720)), (1, (-23 / 72)), (2, (17 / 144)), (3, (5 / 9)), (4, (1 / 3)), (12, (2 / 9)), (25, (-1 / 6)), (31, (-1 / 3)), (33, (-1 / 3)), (45, (1 / 1))]

def value3086 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-35 / 144)), (2, (7 / 144)), (3, (23 / 18)), (4, (5 / 9)), (12, (1 / 3)), (25, (-1 / 6)), (26, (7 / 18)), (31, (-1 / 6)), (33, (-1 / 3)), (43, (1 / 2))]

def value3087 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-23 / 72)), (2, (1 / 32)), (3, (17 / 18)), (4, (1 / 3)), (12, (2 / 3)), (13, (1 / 18)), (26, (1 / 6)), (33, (-1 / 3)), (34, (1 / 18)), (45, (1 / 1)), (50, (1 / 2)), (115, (1 / 1)), (116, (1 / 2))]

def value3088 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-2 / 9)), (2, (13 / 288)), (3, (10 / 9)), (4, (4 / 9)), (12, (5 / 9)), (13, (2 / 9)), (26, (1 / 18)), (33, (-1 / 3)), (34, (1 / 18)), (45, (1 / 2)), (46, (1 / 2)), (114, (1 / 2)), (115, (1 / 1)), (120, (1 / 2))]

def value3089 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-13 / 144)), (2, (5 / 144)), (3, (13 / 18)), (4, (2 / 9)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 18)), (23, (-2 / 3)), (24, (-2 / 3)), (25, (-1 / 6)), (47, (1 / 1)), (48, (1 / 1)), (50, (1 / 2)), (79, (1 / 2)), (94, (1 / 1))]

def value3090 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-19 / 288)), (2, (1 / 24)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (2 / 9)), (13, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 6)), (27, (1 / 12)), (47, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value3091 : Sparse (Fin 909) := [(0, (19 / 480)), (1, (-29 / 72)), (2, (25 / 288)), (3, (13 / 18)), (4, (5 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 3)), (13, (1 / 9)), (24, (-1 / 3)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 3)), (49, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value3092 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 144)), (2, (1 / 32)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (27, (1 / 8)), (48, (1 / 2)), (51, (-1 / 6))]

def value3093 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-49 / 288)), (2, (19 / 288)), (3, (7 / 18)), (4, (5 / 18)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 6)), (24, (-1 / 3)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 3)), (33, (-1 / 3)), (49, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value3094 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-91 / 288)), (2, (5 / 48)), (3, (13 / 18)), (4, (5 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (31, (-2 / 3)), (47, (1 / 2)), (51, (-1 / 6))]

def value3095 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-59 / 288)), (2, (11 / 144)), (3, (13 / 18)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 3)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-5 / 6)), (27, (1 / 12)), (31, (-2 / 3)), (33, (-1 / 3)), (48, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 6))]

def value3096 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-23 / 144)), (2, (1 / 36)), (3, (8 / 9)), (4, (4 / 9)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 24)), (55, (-1 / 3))]

def value3097 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 144)), (2, (7 / 288)), (3, (7 / 18)), (4, (1 / 9)), (12, (5 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 24)), (33, (-1 / 3)), (55, (-1 / 3))]

def value3098 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 4)), (2, (1 / 48)), (3, (25 / 18)), (4, (4 / 9)), (12, (5 / 9)), (13, (7 / 18)), (25, (-1 / 6)), (33, (-1 / 3)), (50, (1 / 2))]

def value3099 : Sparse (Fin 909) := [(0, (29 / 1440)), (1, (-11 / 32)), (2, (7 / 144)), (3, (1 / 1)), (4, (5 / 9)), (12, (1 / 2)), (13, (1 / 9)), (25, (-5 / 6)), (31, (-2 / 3)), (33, (-1 / 3)), (50, (1 / 2))]

def value3100 : Sparse (Fin 909) := [(0, (11 / 360)), (1, (-11 / 36)), (2, (5 / 72)), (3, (2 / 3)), (4, (2 / 3)), (12, (2 / 9)), (25, (-1 / 3)), (31, (-1 / 1)), (33, (-1 / 3))]

def value3101 : Sparse (Fin 909) := [(0, (-1 / 720)), (3, (7 / 18)), (5, (-1 / 36)), (6, (1 / 144)), (8, (1 / 9)), (10, (-1 / 6)), (26, (1 / 9)), (35, (5 / 18)), (36, (1 / 2)), (55, (-1 / 6)), (72, (1 / 2)), (83, (1 / 1)), (228, (-1 / 3)), (316, (1 / 1)), (498, (1 / 2)), (501, (1 / 1)), (727, (-1 / 6))]

def value3102 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (1 / 16)), (3, (7 / 18)), (5, (-7 / 72)), (7, (4 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (35, (5 / 9)), (38, (1 / 2)), (52, (2 / 9)), (59, (-1 / 6)), (72, (1 / 2)), (73, (1 / 1)), (81, (-1 / 3)), (84, (1 / 1)), (318, (1 / 1)), (499, (1 / 2))]

def value3103 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 12)), (2, (5 / 36)), (3, (1 / 6)), (5, (-1 / 4)), (6, (1 / 96)), (7, (4 / 9)), (8, (1 / 3)), (35, (1 / 6)), (39, (1 / 2)), (52, (1 / 9)), (74, (1 / 2)), (81, (-1 / 3)), (85, (1 / 1)), (319, (1 / 1)), (500, (1 / 2))]

def value3104 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 48)), (3, (2 / 9)), (5, (-5 / 72)), (7, (5 / 18)), (8, (1 / 9)), (10, (-1 / 6)), (35, (1 / 3)), (67, (1 / 18)), (69, (1 / 9)), (70, (1 / 18)), (72, (1 / 2)), (287, (1 / 2)), (308, (-1 / 6)), (425, (1 / 2))]

def value3105 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 24)), (2, (11 / 96)), (3, (5 / 9)), (5, (-13 / 72)), (7, (5 / 9)), (8, (2 / 9)), (26, (1 / 18)), (35, (5 / 9)), (51, (-1 / 6)), (52, (1 / 3)), (59, (-1 / 6)), (67, (1 / 18)), (81, (-1 / 3)), (104, (1 / 2)), (425, (1 / 2)), (499, (1 / 2))]

def value3106 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (13 / 96)), (2, (3 / 16)), (3, (2 / 9)), (5, (-19 / 72)), (6, (5 / 288)), (7, (7 / 18)), (8, (7 / 18)), (35, (1 / 6)), (52, (2 / 9)), (81, (-2 / 3)), (100, (1 / 2)), (238, (-1 / 6)), (307, (-1 / 6)), (426, (1 / 2)), (500, (1 / 2))]

def value3107 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 288)), (2, (7 / 144)), (3, (5 / 18)), (4, (1 / 9)), (5, (-5 / 72)), (6, (1 / 144)), (7, (2 / 9)), (12, (1 / 18)), (26, (1 / 6)), (33, (-1 / 6)), (35, (1 / 9)), (54, (-1 / 6)), (81, (-1 / 3)), (85, (1 / 1)), (228, (-1 / 3)), (307, (-1 / 6)), (330, (1 / 1)), (426, (1 / 2)), (498, (1 / 2)), (508, (1 / 1)), (727, (-1 / 6))]

def value3108 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (13 / 144)), (2, (5 / 36)), (3, (4 / 9)), (5, (-23 / 72)), (6, (1 / 144)), (7, (8 / 9)), (8, (4 / 9)), (10, (-1 / 2)), (12, (1 / 18)), (13, (1 / 6)), (35, (1 / 2)), (59, (-1 / 6)), (72, (1 / 2)), (74, (1 / 1)), (81, (-1 / 3)), (82, (1 / 18)), (199, (-1 / 6)), (307, (-1 / 6)), (426, (1 / 2))]

def value3109 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 36)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 9)), (35, (5 / 18)), (37, (1 / 1)), (52, (1 / 18)), (55, (-1 / 3)), (59, (-1 / 6)), (73, (1 / 1)), (84, (1 / 2)), (228, (-1 / 6)), (321, (1 / 2)), (501, (1 / 1)), (503, (1 / 1)), (727, (-1 / 6))]

def value3110 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 288)), (2, (1 / 16)), (3, (7 / 18)), (5, (-1 / 8)), (6, (1 / 288)), (7, (4 / 9)), (8, (1 / 6)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (35, (7 / 18)), (51, (-1 / 3)), (52, (1 / 6)), (59, (-1 / 3)), (69, (1 / 18)), (70, (1 / 18)), (73, (1 / 2)), (81, (-1 / 6)), (259, (-1 / 6)), (308, (-1 / 6)), (322, (1 / 2))]

def value3111 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 12)), (2, (65 / 288)), (3, (7 / 18)), (5, (-11 / 36)), (6, (1 / 144)), (7, (2 / 3)), (8, (11 / 18)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (2 / 9)), (51, (-1 / 6)), (52, (1 / 9)), (59, (-1 / 6)), (81, (-1 / 3)), (86, (1 / 2)), (107, (1 / 2)), (238, (-1 / 6)), (307, (-1 / 6)), (326, (1 / 2)), (428, (1 / 2))]

def value3112 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (17 / 288)), (2, (7 / 48)), (3, (1 / 3)), (5, (-1 / 4)), (6, (1 / 96)), (7, (1 / 2)), (8, (7 / 18)), (35, (2 / 9)), (42, (1 / 2)), (52, (2 / 9)), (76, (1 / 2)), (81, (-1 / 2)), (86, (1 / 2)), (326, (1 / 1)), (506, (1 / 2))]

def value3113 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 288)), (2, (1 / 12)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 3)), (8, (1 / 9)), (10, (-1 / 6)), (11, (1 / 18)), (26, (2 / 9)), (35, (5 / 18)), (39, (1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (74, (1 / 2)), (81, (-1 / 3)), (85, (1 / 2)), (228, (-1 / 3)), (330, (1 / 1)), (501, (1 / 2)), (507, (1 / 2)), (508, (1 / 2)), (727, (-1 / 6))]

def value3114 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (5 / 72)), (3, (5 / 9)), (4, (5 / 18)), (5, (-5 / 72)), (7, (1 / 6)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (26, (2 / 9)), (33, (-1 / 6)), (35, (1 / 9)), (40, (1 / 2)), (52, (1 / 18)), (55, (-1 / 6)), (56, (-1 / 6)), (59, (-1 / 6)), (75, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (228, (-1 / 6)), (307, (-1 / 6)), (330, (1 / 2)), (428, (1 / 2)), (501, (1 / 2)), (508, (3 / 2)), (727, (-1 / 6))]

def value3115 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (19 / 288)), (2, (49 / 288)), (3, (13 / 18)), (5, (-1 / 4)), (6, (1 / 96)), (7, (1 / 2)), (8, (7 / 18)), (10, (-1 / 2)), (12, (2 / 9)), (13, (7 / 18)), (33, (-1 / 6)), (35, (4 / 9)), (52, (7 / 18)), (59, (-2 / 3)), (73, (1 / 2)), (75, (1 / 1)), (81, (-1 / 6)), (82, (1 / 18)), (128, (1 / 18)), (201, (-1 / 6)), (307, (-1 / 6)), (428, (1 / 2))]

def value3116 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-7 / 144)), (3, (2 / 9)), (5, (-11 / 72)), (6, (5 / 144)), (7, (1 / 3)), (8, (1 / 9)), (9, (-1 / 36)), (11, (1 / 18)), (26, (7 / 18)), (35, (8 / 9)), (67, (7 / 18)), (68, (1 / 24)), (70, (1 / 6)), (197, (-1 / 6)), (238, (-1 / 6)), (307, (-1 / 3)), (309, (-1 / 6)), (503, (1 / 2)), (727, (-1 / 6))]

def value3117 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-5 / 96)), (3, (1 / 2)), (10, (-1 / 2)), (12, (2 / 9)), (13, (2 / 3)), (38, (3 / 2)), (55, (-1 / 2)), (59, (-1 / 2)), (72, (3 / 2)), (199, (-1 / 6)), (321, (3 / 2)), (505, (1 / 1)), (727, (-1 / 6))]

def value3118 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (3 / 32)), (3, (4 / 9)), (5, (-1 / 9)), (6, (1 / 288)), (7, (7 / 18)), (8, (1 / 3)), (9, (-1 / 72)), (10, (-2 / 3)), (12, (5 / 18)), (13, (2 / 9)), (27, (1 / 6)), (35, (1 / 9)), (51, (-1 / 1)), (55, (-1 / 3)), (59, (-5 / 6)), (68, (1 / 24)), (69, (1 / 18)), (124, (-1 / 6)), (259, (-1 / 3)), (308, (-1 / 3)), (321, (1 / 2)), (727, (-1 / 6))]

def value3119 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-7 / 288)), (2, (7 / 96)), (3, (2 / 3)), (5, (-1 / 8)), (6, (1 / 288)), (7, (1 / 2)), (8, (2 / 9)), (10, (-1 / 3)), (12, (7 / 18)), (13, (2 / 3)), (35, (1 / 3)), (51, (-2 / 3)), (54, (-2 / 3)), (59, (-2 / 3)), (72, (1 / 2)), (74, (1 / 1)), (82, (1 / 18)), (199, (-1 / 2)), (259, (-1 / 3)), (282, (1 / 2)), (308, (-1 / 6)), (723, (-1 / 6))]

def value3120 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-13 / 288)), (2, (3 / 32)), (3, (7 / 9)), (4, (1 / 6)), (5, (-1 / 8)), (6, (1 / 288)), (7, (4 / 9)), (8, (2 / 9)), (10, (-1 / 3)), (11, (1 / 18)), (12, (1 / 6)), (13, (1 / 9)), (26, (2 / 9)), (35, (1 / 3)), (40, (1 / 1)), (52, (1 / 18)), (55, (-1 / 3)), (59, (-1 / 6)), (75, (1 / 1)), (228, (-1 / 6)), (321, (1 / 2)), (508, (2 / 1)), (727, (-1 / 6))]

def value3121 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 144)), (2, (7 / 144)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 6)), (6, (1 / 72)), (7, (4 / 9)), (8, (2 / 9)), (10, (-1 / 6)), (11, (1 / 9)), (26, (1 / 3)), (35, (1 / 3)), (38, (1 / 2)), (55, (-1 / 6)), (72, (1 / 2)), (228, (-1 / 3)), (321, (1 / 1)), (505, (1 / 2)), (508, (1 / 1)), (727, (-1 / 6))]

def value3122 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 144)), (2, (23 / 288)), (3, (5 / 18)), (4, (1 / 18)), (5, (-13 / 72)), (6, (1 / 48)), (7, (1 / 2)), (8, (1 / 3)), (9, (-1 / 36)), (10, (-1 / 3)), (11, (1 / 18)), (26, (1 / 9)), (27, (1 / 12)), (35, (5 / 18)), (55, (-1 / 6)), (68, (1 / 24)), (71, (1 / 6)), (236, (-1 / 6)), (308, (-1 / 6)), (508, (1 / 2)), (727, (-1 / 6))]

def value3123 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (-11 / 144)), (3, (1 / 9)), (5, (-7 / 72)), (6, (1 / 144)), (7, (1 / 3)), (8, (2 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (13, (2 / 9)), (35, (4 / 9)), (52, (1 / 9)), (54, (-1 / 3)), (59, (-1 / 3)), (71, (1 / 9)), (82, (1 / 9)), (199, (-1 / 3)), (259, (-1 / 3)), (723, (-1 / 6))]

def value3124 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (13 / 288)), (2, (7 / 144)), (3, (1 / 3)), (5, (-5 / 72)), (6, (1 / 32)), (7, (1 / 18)), (11, (1 / 18)), (13, (1 / 9)), (26, (1 / 18)), (35, (7 / 18)), (52, (1 / 3)), (128, (1 / 18)), (201, (-1 / 6)), (228, (-1 / 2)), (517, (1 / 2))]

def value3125 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 144)), (2, (5 / 48)), (3, (13 / 18)), (4, (1 / 9)), (5, (-5 / 72)), (7, (2 / 9)), (8, (2 / 9)), (26, (2 / 9)), (33, (-2 / 3)), (51, (-2 / 3)), (55, (-1 / 6)), (126, (-1 / 3)), (137, (1 / 2)), (145, (1 / 2))]

def value3126 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 96)), (2, (19 / 144)), (3, (11 / 18)), (4, (2 / 9)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 6)), (24, (-1 / 6)), (26, (1 / 6)), (107, (1 / 1)), (112, (1 / 1)), (126, (-1 / 6)), (137, (1 / 2)), (146, (1 / 2)), (236, (-1 / 6))]

def value3127 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (13 / 288)), (2, (35 / 288)), (3, (2 / 3)), (5, (-7 / 72)), (6, (1 / 288)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 2)), (26, (1 / 18)), (34, (1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (52, (7 / 18)), (64, (-5 / 6)), (69, (1 / 9)), (125, (-2 / 3)), (126, (-1 / 6)), (138, (1 / 2)), (146, (1 / 2)), (238, (-1 / 6)), (543, (1 / 2))]

def value3128 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 288)), (3, (1 / 2)), (5, (-5 / 72)), (6, (1 / 96)), (7, (1 / 6)), (13, (4 / 9)), (26, (5 / 9)), (34, (7 / 18)), (35, (5 / 18)), (52, (1 / 9)), (64, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 6)), (138, (1 / 2)), (197, (-1 / 6)), (238, (-1 / 3))]

def value3129 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (1 / 24)), (3, (7 / 9)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 18)), (12, (1 / 9)), (13, (7 / 18)), (26, (5 / 18)), (34, (1 / 9)), (35, (1 / 6)), (51, (-1 / 3)), (52, (1 / 6)), (55, (-1 / 6)), (64, (-1 / 6)), (139, (1 / 2)), (204, (1 / 2)), (237, (-1 / 6)), (472, (1 / 1)), (546, (1 / 2)), (736, (1 / 2))]

def value3130 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-7 / 144)), (2, (5 / 144)), (3, (8 / 9)), (4, (1 / 18)), (5, (-1 / 24)), (6, (1 / 144)), (12, (1 / 6)), (13, (1 / 3)), (26, (7 / 18)), (27, (1 / 24)), (34, (7 / 18)), (35, (2 / 9)), (51, (-1 / 6)), (52, (1 / 9)), (55, (-1 / 3)), (64, (-1 / 3)), (139, (1 / 2)), (238, (-1 / 6))]

def value3131 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 96)), (2, (17 / 288)), (3, (5 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 9)), (8, (1 / 18)), (9, (-1 / 72)), (10, (-1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 6)), (27, (5 / 24)), (51, (-1 / 6)), (52, (1 / 18)), (55, (-1 / 2)), (68, (1 / 12)), (69, (1 / 18)), (125, (-1 / 3)), (126, (-1 / 6)), (308, (-1 / 6)), (538, (1 / 2)), (727, (-1 / 6))]

def value3132 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 48)), (2, (37 / 288)), (3, (1 / 2)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 72)), (7, (1 / 6)), (8, (1 / 9)), (9, (-1 / 72)), (13, (1 / 9)), (26, (1 / 9)), (27, (1 / 12)), (31, (-1 / 6)), (33, (-1 / 3)), (35, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6)), (55, (-1 / 3)), (64, (-5 / 6)), (68, (1 / 12)), (69, (1 / 18)), (125, (-1 / 3)), (126, (-1 / 6)), (238, (-2 / 3)), (307, (-1 / 3)), (309, (-1 / 6)), (543, (1 / 2)), (727, (-1 / 6))]

def value3133 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 72)), (2, (1 / 24)), (3, (1 / 9)), (5, (-17 / 72)), (6, (1 / 72)), (8, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (13, (1 / 2)), (35, (1 / 9)), (52, (1 / 6)), (54, (-1 / 6)), (59, (-1 / 3)), (69, (1 / 18)), (82, (1 / 9)), (128, (5 / 18)), (199, (-1 / 6)), (540, (1 / 2)), (721, (-1 / 3)), (723, (-1 / 6))]

def value3134 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-5 / 48)), (2, (1 / 24)), (3, (13 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 6)), (12, (1 / 3)), (13, (1 / 6)), (23, (-1 / 3)), (24, (-1 / 3)), (27, (1 / 12)), (47, (1 / 1)), (51, (-1 / 2)), (52, (1 / 18)), (55, (-1 / 3)), (69, (1 / 18)), (124, (-1 / 6)), (125, (-1 / 6)), (126, (-1 / 6)), (140, (1 / 2)), (205, (1 / 2)), (538, (1 / 1)), (539, (1 / 1))]

def value3135 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-29 / 288)), (2, (1 / 12)), (3, (13 / 18)), (5, (-1 / 12)), (7, (1 / 9)), (12, (5 / 9)), (13, (5 / 18)), (23, (-1 / 3)), (27, (1 / 4)), (51, (-2 / 3)), (55, (-2 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (125, (-1 / 6)), (140, (1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2048 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (-11 / 288)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 9)), (98, (-1 / 2)), (237, (1 / 6))]

def value2049 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (-1 / 144)), (3, (-1 / 18)), (4, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 3)), (52, (-1 / 18)), (54, (1 / 6)), (56, (1 / 6)), (104, (-1 / 2))]

def value2050 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 6)), (4, (-1 / 9)), (12, (-1 / 18)), (50, (-1 / 2)), (177, (-1 / 2)), (209, (-1 / 2))]

def value2051 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (-1 / 48)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 6)), (8, (-1 / 18)), (10, (1 / 6)), (13, (-1 / 18)), (35, (-2 / 9)), (52, (-1 / 18)), (81, (1 / 6)), (82, (-1 / 18)), (306, (1 / 6)), (502, (-1 / 2))]

def value2052 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (13, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (73, (-1 / 2)), (201, (1 / 6)), (324, (-1 / 2)), (517, (-1 / 2))]

def value2053 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 36)), (3, (-1 / 9)), (5, (7 / 72)), (6, (-1 / 96)), (7, (-1 / 6)), (8, (-1 / 18)), (10, (1 / 6)), (13, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 18)), (82, (-1 / 9)), (306, (1 / 6))]

def value2054 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 72)), (3, (-2 / 9)), (13, (-1 / 9)), (35, (-1 / 9)), (52, (-1 / 9)), (75, (-1 / 2)), (201, (1 / 3)), (760, (-1 / 2))]

def value2055 : Sparse (Fin 909) := [(1, (11 / 144)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (17, (-1 / 2)), (24, (1 / 6))]

def value2056 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (23 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 18)), (19, (-1 / 2)), (24, (1 / 6))]

def value2057 : Sparse (Fin 909) := [(0, (-19 / 1440)), (1, (7 / 96)), (2, (-1 / 144)), (3, (-1 / 9)), (4, (-1 / 6)), (20, (-1 / 2)), (24, (1 / 6))]

def value2058 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (1 / 72)), (3, (-1 / 9)), (5, (1 / 18)), (6, (-1 / 96)), (7, (-1 / 18)), (11, (-1 / 9)), (26, (-1 / 9)), (35, (-1 / 6)), (52, (-1 / 6)), (228, (1 / 3))]

def value2059 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (-1 / 72)), (3, (-1 / 6)), (4, (-1 / 6)), (26, (-1 / 18)), (31, (1 / 6)), (99, (-1 / 2)), (107, (-1 / 2))]

def value2060 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (-1 / 48)), (3, (-2 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (81, (1 / 2)), (228, (1 / 6)), (709, (-1 / 2))]

def value2061 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (2, (-1 / 36)), (7, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 18)), (51, (1 / 6)), (104, (-1 / 2))]

def value2062 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (81, (1 / 6)), (85, (-1 / 1)), (228, (1 / 3))]

def value2063 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (11 / 288)), (2, (-5 / 96)), (3, (-5 / 18)), (4, (-1 / 6)), (26, (-2 / 9))]

def value2064 : Sparse (Fin 909) := [(1, (1 / 36)), (3, (-5 / 18)), (26, (-1 / 6)), (37, (-1 / 2)), (56, (1 / 6))]

def value2065 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (13 / 96)), (3, (-1 / 3)), (4, (-1 / 6)), (12, (-5 / 18))]

def value2066 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (1 / 18)), (4, (-1 / 18)), (12, (-1 / 18)), (43, (-1 / 2)), (113, (-1 / 2)), (114, (-1 / 2))]

def value2067 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (1 / 36)), (3, (-1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (11, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 6)), (67, (-1 / 6)), (702, (-1 / 2))]

def value2068 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (1 / 96)), (3, (-1 / 6)), (4, (-1 / 9)), (13, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 9)), (56, (1 / 3)), (190, (-1 / 2)), (453, (-1 / 2))]

def value2069 : Sparse (Fin 909) := [(1, (7 / 144)), (2, (-1 / 144)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-2 / 9)), (53, (-1 / 2))]

def value2070 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (17 / 288)), (2, (-1 / 48)), (3, (-4 / 9)), (4, (-2 / 9)), (26, (-5 / 18))]

def value2071 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (13 / 96)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-2 / 9)), (31, (1 / 6))]

def value2072 : Sparse (Fin 909) := [(1, (1 / 36)), (3, (-1 / 9)), (4, (1 / 6)), (31, (1 / 6))]

def value2073 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 32)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (21, (-1 / 2))]

def value2074 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (11 / 288)), (2, (-1 / 144)), (3, (-5 / 18)), (4, (-2 / 9)), (26, (-2 / 9)), (53, (-1 / 2)), (119, (-1 / 2))]

def value2075 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 36)), (2, (1 / 288)), (3, (-1 / 6)), (4, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 9)), (34, (-1 / 6)), (35, (-1 / 18)), (190, (-1 / 2))]

def value2076 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (3 / 32)), (3, (-1 / 9)), (4, (-2 / 9)), (12, (-1 / 18)), (22, (-1 / 2)), (31, (1 / 6))]

def value2077 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 32)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (7, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (55, (1 / 3)), (113, (-1 / 2))]

def value2078 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (25, (1 / 6)), (48, (-1 / 2)), (50, (-1 / 2)), (177, (-1 / 2))]

def value2079 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 9)), (7, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (83, (-1 / 2)), (84, (-1 / 2)), (228, (1 / 6)), (702, (-1 / 2))]

def value2080 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (-1 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (43, (-1 / 2)), (44, (-1 / 2)), (114, (-1 / 2))]

def value2081 : Sparse (Fin 909) := [(53, (-1 / 2)), (84, (-1 / 2)), (702, (-1 / 2)), (709, (-1 / 2))]

def value2082 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-1 / 3)), (4, (-1 / 9)), (12, (-1 / 6)), (13, (-1 / 9)), (26, (-1 / 18)), (33, (1 / 6)), (35, (-1 / 18)), (55, (1 / 3)), (177, (-1 / 2))]

def value2083 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (7, (-1 / 9)), (11, (-1 / 18)), (26, (-2 / 9)), (35, (-1 / 6)), (81, (1 / 6)), (228, (1 / 3)), (709, (-1 / 2))]

def value2084 : Sparse (Fin 909) := [(0, (-13 / 720)), (1, (17 / 144)), (3, (-2 / 9)), (4, (-2 / 9)), (12, (-1 / 18))]

def value2085 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (5 / 36)), (3, (-1 / 9)), (4, (-1 / 9)), (12, (-1 / 6)), (22, (-1 / 2))]

def value2086 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (3, (-5 / 18)), (4, (-1 / 9)), (26, (-2 / 9)), (35, (-1 / 18)), (55, (1 / 3)), (191, (-1 / 2))]

def value2087 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (7 / 144)), (3, (-1 / 9)), (4, (1 / 6)), (18, (-1 / 2))]

def value2088 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (25 / 288)), (4, (-1 / 18)), (22, (-1 / 2))]

def value2089 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (1 / 8)), (2, (-1 / 32)), (3, (-1 / 3)), (4, (-1 / 6)), (12, (-1 / 6)), (27, (-1 / 8)), (31, (1 / 2)), (51, (1 / 1)), (55, (1 / 2)), (194, (-1 / 1)), (486, (-1 / 1)), (487, (-1 / 1))]

def value2090 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 96)), (2, (-1 / 96)), (3, (-1 / 6)), (12, (-1 / 6)), (23, (1 / 1)), (24, (1 / 2)), (25, (1 / 2)), (27, (-1 / 8)), (54, (1 / 2)), (55, (1 / 2)), (195, (-1 / 1)), (263, (-1 / 1)), (487, (-1 / 1))]

def value2091 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (1 / 6)), (2, (-1 / 48)), (3, (-7 / 6)), (4, (-1 / 6)), (12, (-2 / 3)), (13, (-5 / 6)), (33, (1 / 1)), (51, (1 / 2)), (55, (1 / 2)), (59, (1 / 2)), (61, (1 / 2)), (194, (-1 / 1))]

def value2092 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (1 / 8)), (2, (-1 / 16)), (23, (1 / 1)), (24, (2 / 1)), (27, (-3 / 4)), (30, (1 / 1)), (55, (1 / 1)), (194, (-1 / 1))]

def value2093 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (5 / 24)), (2, (-1 / 24)), (3, (-4 / 3)), (4, (-1 / 3)), (12, (-5 / 6)), (13, (-1 / 3)), (23, (1 / 2)), (25, (1 / 1)), (31, (1 / 2)), (33, (2 / 1)), (54, (1 / 1)), (62, (1 / 2))]

def value2094 : Sparse (Fin 909) := [(0, (1 / 40)), (1, (5 / 16)), (2, (-1 / 16)), (3, (-2 / 1)), (4, (-1 / 3)), (12, (-1 / 1)), (13, (-2 / 1)), (32, (-1 / 6))]

def value2095 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 24)), (2, (-1 / 48)), (23, (1 / 1)), (24, (1 / 1)), (27, (-1 / 4)), (55, (2 / 1)), (63, (1 / 1)), (65, (1 / 1))]

def value2096 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (1 / 12)), (2, (-1 / 32)), (3, (-1 / 1)), (4, (-1 / 6)), (7, (-1 / 6)), (12, (-1 / 2)), (23, (1 / 1)), (25, (1 / 1)), (26, (-1 / 6)), (33, (1 / 1)), (51, (1 / 2)), (54, (1 / 1)), (55, (1 / 2)), (63, (1 / 2)), (64, (1 / 2)), (65, (1 / 2))]

def value2097 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (5 / 24)), (2, (-3 / 32)), (3, (-4 / 3)), (4, (-1 / 3)), (12, (-2 / 3)), (13, (-2 / 3)), (26, (-1 / 6)), (33, (1 / 1)), (34, (-1 / 6))]

def value2098 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (5 / 16)), (2, (-1 / 16)), (3, (-2 / 1)), (12, (-1 / 1)), (13, (-2 / 1)), (34, (-1 / 3))]

def value2099 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 8)), (2, (-1 / 12)), (3, (-7 / 6)), (4, (-2 / 3)), (12, (-1 / 3)), (25, (1 / 1)), (26, (-1 / 6)), (31, (1 / 1)), (33, (3 / 2))]

def value2100 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 8)), (2, (-1 / 16)), (3, (-7 / 6)), (4, (-1 / 2)), (12, (-1 / 3)), (13, (-1 / 6)), (25, (1 / 2)), (26, (-1 / 2)), (31, (1 / 2)), (33, (1 / 2)), (34, (-1 / 6))]

def value2101 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (5 / 24)), (2, (-1 / 48)), (3, (-1 / 1)), (4, (-1 / 2)), (12, (-1 / 3)), (23, (1 / 2)), (25, (1 / 1)), (26, (-1 / 3)), (31, (1 / 2)), (33, (1 / 1)), (54, (1 / 1)), (65, (1 / 2)), (195, (-1 / 1))]

def value2102 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (7 / 32)), (2, (-5 / 48)), (3, (-3 / 2)), (4, (-1 / 2)), (12, (-2 / 3)), (26, (-1 / 3)), (33, (3 / 2)), (81, (1 / 2)), (195, (-1 / 1))]

def value2103 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 48)), (2, (-1 / 32)), (3, (-2 / 3)), (4, (-1 / 3)), (25, (1 / 1)), (26, (-1 / 3)), (31, (1 / 2)), (33, (1 / 1)), (63, (1 / 2)), (64, (1 / 1)), (123, (1 / 2))]

def value2104 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (13 / 48)), (2, (-1 / 24)), (3, (-7 / 6)), (4, (-1 / 2)), (12, (-1 / 2)), (25, (1 / 1)), (26, (-1 / 6)), (31, (1 / 1)), (33, (3 / 2)), (51, (1 / 2)), (55, (1 / 2)), (64, (1 / 2)), (123, (1 / 2))]

def value2105 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (19 / 48)), (2, (-1 / 12)), (3, (-4 / 3)), (4, (-2 / 3)), (12, (-2 / 3)), (13, (-1 / 3)), (25, (1 / 1)), (31, (1 / 1)), (33, (1 / 1))]

def value2106 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (1 / 32)), (3, (-1 / 2)), (5, (1 / 8)), (6, (-1 / 32)), (12, (-1 / 6)), (13, (-1 / 1)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 2)), (52, (-1 / 3)), (55, (1 / 2)), (63, (1 / 1)), (82, (-1 / 6)), (123, (1 / 2)), (128, (-1 / 6)), (237, (1 / 2)), (306, (1 / 2)), (721, (1 / 2))]

def value2107 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 32)), (3, (-1 / 6)), (5, (1 / 6)), (6, (-5 / 96)), (7, (-1 / 3)), (13, (-1 / 3)), (35, (-1 / 2)), (52, (-1 / 3)), (54, (1 / 1)), (59, (1 / 2)), (82, (-1 / 6)), (128, (-1 / 6)), (199, (1 / 2)), (228, (1 / 1)), (271, (1 / 1)), (721, (1 / 1))]

def value2108 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 32)), (2, (-17 / 96)), (3, (-1 / 2)), (5, (7 / 24)), (6, (-1 / 24)), (8, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 1)), (33, (1 / 2)), (35, (-1 / 3)), (52, (-5 / 6)), (59, (3 / 2)), (60, (-1 / 6)), (82, (-1 / 6)), (128, (-1 / 2)), (201, (1 / 2)), (490, (1 / 2)), (721, (1 / 2))]

def value2109 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 48)), (2, (-1 / 32)), (3, (-1 / 1)), (7, (-1 / 2)), (12, (-1 / 2)), (13, (-2 / 3)), (23, (3 / 2)), (35, (-1 / 2)), (54, (3 / 2)), (70, (-1 / 6)), (125, (3 / 2)), (196, (1 / 1))]

def value2110 : Sparse (Fin 909) := [(1, (7 / 48)), (2, (5 / 96)), (3, (-5 / 6)), (4, (-1 / 3)), (5, (1 / 24)), (6, (-1 / 96)), (7, (-1 / 3)), (13, (-1 / 6)), (24, (1 / 1)), (26, (-1 / 3)), (35, (-1 / 2)), (55, (1 / 2)), (56, (1 / 1)), (70, (-1 / 6)), (125, (1 / 2)), (197, (2 / 1))]

def value2111 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 24)), (2, (1 / 24)), (3, (-1 / 2)), (5, (1 / 12)), (6, (-1 / 48)), (7, (-1 / 6)), (12, (-1 / 6)), (13, (-1 / 6)), (23, (1 / 2)), (26, (-1 / 3)), (35, (-1 / 2)), (54, (1 / 2)), (55, (1 / 1)), (70, (-1 / 6)), (125, (1 / 1)), (196, (1 / 2)), (197, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3136 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 36)), (2, (7 / 144)), (3, (1 / 1)), (4, (5 / 18)), (12, (11 / 18)), (13, (5 / 18)), (17, (1 / 1)), (23, (-1 / 3)), (26, (1 / 9)), (35, (1 / 18)), (40, (1 / 1)), (51, (-1 / 6)), (52, (1 / 18)), (55, (-1 / 2)), (125, (-1 / 6)), (140, (1 / 2)), (146, (2 / 1))]

def value3137 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-7 / 48)), (2, (7 / 144)), (3, (2 / 3)), (7, (2 / 9)), (12, (4 / 9)), (13, (5 / 9)), (16, (1 / 2)), (23, (-1 / 2)), (35, (1 / 9)), (38, (1 / 1)), (51, (-1 / 3)), (54, (-2 / 3)), (124, (-1 / 6)), (140, (1 / 2)), (141, (1 / 2)), (196, (-1 / 6))]

def value3138 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (-13 / 144)), (2, (7 / 144)), (3, (7 / 9)), (4, (1 / 9)), (12, (1 / 3)), (13, (2 / 9)), (16, (1 / 2)), (23, (-1 / 6)), (26, (1 / 9)), (35, (1 / 9)), (38, (1 / 2)), (51, (-1 / 3)), (52, (1 / 9)), (55, (-1 / 2)), (125, (-1 / 6)), (140, (1 / 1)), (141, (1 / 2)), (146, (1 / 1))]

def value3139 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (13 / 96)), (3, (11 / 18)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 288)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 6)), (13, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 24)), (31, (-1 / 6)), (35, (1 / 18)), (51, (-5 / 6)), (52, (5 / 18)), (55, (-1 / 6)), (69, (1 / 9)), (125, (-1 / 6)), (126, (-2 / 3)), (146, (1 / 2)), (208, (1 / 2)), (238, (-1 / 6)), (538, (1 / 2))]

def value3140 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (7 / 96)), (2, (11 / 96)), (3, (7 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 18)), (12, (1 / 9)), (13, (4 / 9)), (38, (1 / 2)), (51, (-1 / 3)), (52, (5 / 18)), (54, (-1 / 6)), (69, (1 / 18)), (126, (-1 / 3)), (128, (1 / 18)), (237, (-1 / 3)), (539, (1 / 1)), (540, (1 / 2))]

def value3141 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 36)), (2, (1 / 32)), (3, (4 / 9)), (4, (2 / 9)), (5, (-1 / 36)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 6)), (15, (1 / 2)), (24, (-1 / 2)), (33, (-1 / 6)), (39, (1 / 1)), (51, (-1 / 3)), (56, (-2 / 3)), (126, (-1 / 6)), (144, (1 / 2)), (145, (1 / 2)), (197, (-1 / 6))]

def value3142 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 288)), (2, (13 / 96)), (3, (7 / 18)), (4, (1 / 9)), (5, (-5 / 72)), (7, (1 / 18)), (8, (1 / 9)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 8)), (31, (-2 / 3)), (33, (-5 / 6)), (51, (-2 / 3)), (55, (-1 / 3)), (64, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 6)), (126, (-1 / 6)), (145, (1 / 2)), (238, (-1 / 3))]

def value3143 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 8)), (2, (1 / 36)), (3, (11 / 18)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 96)), (8, (1 / 9)), (12, (1 / 6)), (13, (1 / 6)), (23, (-1 / 6)), (26, (1 / 9)), (27, (1 / 8)), (35, (1 / 18)), (52, (1 / 9)), (55, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 6)), (146, (1 / 2)), (236, (-1 / 6))]

def value3144 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 8)), (2, (31 / 288)), (3, (8 / 9)), (4, (1 / 6)), (5, (-1 / 24)), (6, (1 / 288)), (12, (1 / 3)), (13, (5 / 18)), (25, (-1 / 3)), (26, (1 / 18)), (27, (1 / 12)), (31, (-2 / 3)), (33, (-5 / 6)), (35, (1 / 18)), (51, (-2 / 3)), (52, (1 / 9)), (55, (-1 / 3)), (64, (-1 / 3)), (142, (1 / 2)), (238, (-1 / 6))]

def value3145 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (-5 / 144)), (2, (13 / 144)), (3, (5 / 9)), (4, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 18)), (27, (1 / 24)), (31, (-1 / 3)), (43, (1 / 2)), (51, (-1 / 2)), (52, (1 / 6)), (55, (-1 / 6)), (95, (1 / 1)), (237, (-1 / 6)), (546, (1 / 2)), (738, (1 / 2))]

def value3146 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-35 / 288)), (2, (7 / 96)), (3, (7 / 6)), (4, (5 / 18)), (12, (4 / 9)), (13, (13 / 18)), (18, (1 / 2)), (26, (1 / 18)), (33, (-1 / 6)), (35, (1 / 18)), (42, (1 / 1)), (51, (-1 / 2)), (52, (1 / 18)), (54, (-1 / 6)), (56, (-1 / 3)), (142, (1 / 2)), (143, (1 / 2))]

def value3147 : Sparse (Fin 909) := [(0, (-11 / 720)), (1, (1 / 18)), (2, (37 / 288)), (3, (11 / 18)), (5, (-7 / 36)), (6, (7 / 288)), (8, (1 / 9)), (12, (2 / 9)), (13, (13 / 18)), (33, (-1 / 3)), (51, (-1 / 6)), (52, (4 / 9)), (54, (-1 / 6)), (59, (-1 / 3)), (102, (1 / 2)), (128, (1 / 9)), (721, (-1 / 6)), (739, (1 / 2))]

def value3148 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-11 / 144)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 6)), (12, (2 / 9)), (13, (1 / 9)), (23, (-1 / 6)), (42, (1 / 1)), (51, (-1 / 3)), (56, (-1 / 3)), (97, (1 / 1)), (110, (1 / 1)), (124, (-1 / 6)), (140, (1 / 2)), (144, (1 / 2)), (197, (-1 / 6))]

def value3149 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-1 / 18)), (2, (1 / 32)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (2 / 9)), (13, (1 / 3)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 18)), (38, (1 / 2)), (39, (1 / 2)), (42, (1 / 2)), (47, (1 / 2)), (51, (-1 / 6)), (54, (-1 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (110, (1 / 1)), (143, (1 / 2))]

def value3150 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 32)), (2, (7 / 96)), (3, (1 / 2)), (5, (-1 / 6)), (6, (1 / 144)), (7, (4 / 9)), (8, (2 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 6)), (35, (11 / 18)), (52, (2 / 9)), (59, (-1 / 2)), (72, (1 / 2)), (73, (1 / 1)), (81, (-1 / 3)), (82, (1 / 18)), (199, (-1 / 6)), (284, (1 / 1)), (306, (-1 / 6)), (499, (1 / 2)), (502, (1 / 1))]

def value3151 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-5 / 288)), (2, (1 / 24)), (3, (1 / 2)), (4, (1 / 6)), (5, (-7 / 72)), (6, (1 / 144)), (7, (1 / 3)), (8, (1 / 18)), (11, (1 / 18)), (26, (5 / 18)), (35, (5 / 9)), (37, (1 / 2)), (52, (2 / 9)), (73, (1 / 2)), (81, (-1 / 3)), (83, (1 / 2)), (84, (1 / 1)), (228, (-1 / 2)), (317, (1 / 1)), (517, (1 / 2)), (709, (1 / 2))]

def value3152 : Sparse (Fin 909) := [(0, (13 / 720)), (1, (-65 / 288)), (2, (13 / 288)), (3, (2 / 3)), (4, (5 / 9)), (7, (1 / 9)), (12, (1 / 9)), (17, (1 / 2)), (20, (1 / 2)), (23, (-1 / 6)), (24, (-2 / 3)), (25, (-1 / 3)), (26, (1 / 18)), (31, (-1 / 6)), (44, (1 / 2)), (48, (1 / 2))]

def value3153 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-49 / 288)), (2, (7 / 288)), (3, (13 / 18)), (4, (5 / 18)), (7, (1 / 18)), (12, (5 / 18)), (15, (1 / 2)), (18, (1 / 2)), (19, (1 / 2)), (21, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (37, (1 / 1)), (47, (1 / 2)), (48, (1 / 2))]

def value3154 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-1 / 48)), (2, (5 / 144)), (3, (11 / 18)), (4, (2 / 9)), (7, (1 / 18)), (12, (1 / 3)), (14, (1 / 2)), (15, (3 / 2)), (23, (-1 / 2)), (24, (-1 / 6)), (25, (-1 / 2)), (36, (1 / 1)), (48, (1 / 1))]

def value3155 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-1 / 9)), (2, (1 / 18)), (14, (1 / 2)), (17, (1 / 1)), (23, (-5 / 6)), (25, (-4 / 3)), (27, (1 / 24)), (31, (-2 / 3))]

def value3156 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-59 / 288)), (2, (1 / 288)), (3, (13 / 18)), (4, (1 / 3)), (12, (5 / 18)), (15, (1 / 1)), (16, (1 / 2)), (18, (1 / 1)), (23, (-1 / 6)), (25, (-1 / 2)), (38, (1 / 1)), (50, (1 / 2))]

def value3157 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-35 / 72)), (3, (8 / 9)), (4, (4 / 9)), (12, (4 / 9)), (16, (1 / 2)), (17, (1 / 1)), (23, (-1 / 2))]

def value3158 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 36)), (2, (7 / 72)), (3, (1 / 2)), (5, (-5 / 24)), (6, (1 / 288)), (7, (1 / 2)), (8, (4 / 9)), (26, (1 / 18)), (35, (1 / 2)), (52, (1 / 9)), (59, (-1 / 6)), (67, (1 / 18)), (73, (1 / 2)), (81, (-1 / 2)), (428, (1 / 2))]

def value3159 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (17 / 288)), (2, (1 / 9)), (3, (4 / 9)), (5, (-17 / 72)), (6, (1 / 72)), (7, (7 / 18)), (8, (1 / 2)), (13, (1 / 18)), (35, (1 / 3)), (52, (1 / 3)), (59, (-1 / 2)), (69, (1 / 9)), (70, (1 / 18)), (81, (-1 / 3)), (201, (-1 / 6)), (287, (1 / 2)), (306, (-1 / 6)), (308, (-1 / 6)), (499, (1 / 2))]

def value3160 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (25 / 288)), (2, (17 / 144)), (3, (1 / 3)), (5, (-17 / 72)), (6, (1 / 48)), (7, (5 / 9)), (8, (1 / 3)), (10, (-1 / 6)), (12, (1 / 9)), (13, (1 / 3)), (35, (5 / 9)), (52, (2 / 9)), (54, (-1 / 6)), (59, (-2 / 3)), (74, (1 / 2)), (81, (-1 / 6)), (82, (1 / 9)), (199, (-1 / 2)), (306, (-1 / 6)), (500, (1 / 2)), (502, (1 / 2))]

def value3161 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 144)), (2, (-1 / 72)), (3, (2 / 9)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 3)), (37, (1 / 2)), (56, (-1 / 6))]

def value3162 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (13 / 144)), (2, (49 / 288)), (3, (1 / 2)), (5, (-7 / 36)), (6, (1 / 48)), (7, (7 / 18)), (13, (1 / 18)), (35, (5 / 9)), (52, (1 / 2)), (60, (1 / 18)), (81, (-1 / 3)), (98, (1 / 2)), (237, (-1 / 6)), (306, (-1 / 6)), (392, (1 / 2)), (499, (1 / 2))]

def value3163 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 32)), (2, (23 / 288)), (3, (5 / 9)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (12, (2 / 9)), (13, (2 / 3)), (23, (-1 / 6)), (27, (1 / 24)), (35, (1 / 3)), (51, (-1 / 3)), (52, (4 / 9)), (54, (-1 / 2)), (62, (-1 / 3)), (98, (1 / 2)), (237, (-1 / 6))]

def value3164 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 12)), (2, (1 / 8)), (3, (7 / 9)), (5, (-7 / 36)), (6, (7 / 288)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 6)), (13, (13 / 18)), (35, (5 / 9)), (52, (11 / 18)), (59, (-1 / 6)), (60, (1 / 18)), (75, (1 / 2)), (81, (-1 / 6)), (82, (1 / 9)), (128, (1 / 6)), (201, (-1 / 2)), (306, (-1 / 6)), (399, (1 / 2)), (502, (1 / 2)), (760, (1 / 2))]

def value3165 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (5 / 36)), (2, (-1 / 36)), (14, (1 / 2)), (23, (-2 / 3)), (25, (-2 / 3)), (27, (1 / 12))]

def value3166 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-19 / 144)), (2, (5 / 144)), (3, (1 / 2)), (4, (2 / 9)), (12, (5 / 18)), (15, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 6)), (27, (1 / 24))]

def value3167 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-1 / 18)), (2, (1 / 36)), (17, (1 / 2)), (23, (-1 / 6)), (25, (-1 / 2)), (27, (1 / 24)), (30, (-1 / 6)), (31, (-2 / 3))]

def value3168 : Sparse (Fin 909) := [(0, (11 / 360)), (1, (-1 / 24)), (2, (1 / 24)), (3, (2 / 3)), (12, (-1 / 18)), (16, (1 / 2)), (23, (-1 / 3)), (27, (1 / 24))]

def value3169 : Sparse (Fin 909) := [(0, (7 / 240)), (1, (-13 / 72)), (2, (1 / 16)), (3, (1 / 3)), (4, (2 / 9)), (12, (1 / 3)), (17, (1 / 2)), (23, (-1 / 6)), (27, (1 / 24)), (30, (-1 / 6))]

def value3170 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-13 / 72)), (2, (11 / 288)), (3, (7 / 9)), (4, (5 / 9)), (12, (4 / 9)), (15, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 3))]

def value3171 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 288)), (2, (-1 / 96)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (23, (-1 / 3)), (25, (-1 / 6)), (26, (1 / 9)), (27, (1 / 12)), (54, (-1 / 3)), (64, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 2)), (126, (-1 / 3))]

def value3172 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 9)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 3)), (26, (1 / 6)), (35, (5 / 9)), (52, (1 / 2)), (67, (1 / 18)), (81, (-1 / 2)), (84, (1 / 2)), (228, (-1 / 6)), (460, (1 / 2))]

def value3173 : Sparse (Fin 909) := [(0, (7 / 288)), (1, (-11 / 96)), (2, (1 / 48)), (3, (2 / 3)), (4, (2 / 9)), (12, (1 / 18)), (18, (1 / 2))]

def value3174 : Sparse (Fin 909) := [(0, (1 / 32)), (1, (-107 / 288)), (2, (1 / 48)), (3, (8 / 9)), (4, (1 / 2)), (12, (7 / 18)), (18, (1 / 2)), (25, (-1 / 3)), (31, (-1 / 6))]

def value3175 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-25 / 288)), (2, (7 / 144)), (3, (5 / 9)), (4, (1 / 18)), (5, (-1 / 36)), (7, (5 / 18)), (12, (1 / 9)), (23, (-1 / 1)), (24, (-5 / 6)), (26, (1 / 18)), (27, (1 / 12)), (35, (1 / 9)), (55, (-1 / 2)), (69, (1 / 18)), (70, (1 / 18)), (79, (1 / 1)), (113, (1 / 2)), (124, (-1 / 6)), (125, (-1 / 6)), (126, (-1 / 6)), (197, (-1 / 6)), (291, (1 / 2)), (640, (1 / 2)), (751, (1 / 2))]

def value3176 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (1 / 144)), (3, (5 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 3)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 6)), (26, (1 / 18)), (35, (2 / 9)), (51, (-1 / 3)), (52, (1 / 18)), (54, (-1 / 3)), (56, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (97, (1 / 2)), (100, (1 / 2)), (104, (1 / 2)), (124, (-1 / 6)), (125, (-1 / 6)), (126, (-1 / 6)), (197, (-1 / 6)), (291, (1 / 2)), (300, (1 / 1)), (538, (1 / 2)), (643, (1 / 2))]

def value3177 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 144)), (3, (2 / 9)), (5, (-1 / 18)), (6, (5 / 144)), (7, (1 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 9)), (54, (-1 / 3)), (69, (1 / 18)), (70, (1 / 18)), (72, (1 / 2)), (82, (1 / 6)), (199, (-1 / 3)), (306, (-1 / 6)), (498, (1 / 2)), (505, (1 / 2))]

def value3178 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 72)), (2, (1 / 48)), (3, (7 / 18)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 18)), (10, (-1 / 6)), (12, (5 / 18)), (13, (13 / 18)), (33, (-1 / 3)), (35, (1 / 6)), (38, (1 / 1)), (52, (1 / 9)), (54, (-1 / 2)), (59, (-1 / 3)), (72, (1 / 2)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 3)), (306, (-1 / 6)), (313, (1 / 1)), (498, (1 / 2)), (505, (1 / 1)), (540, (1 / 1)), (721, (-1 / 3)), (723, (-1 / 6))]

def value3179 : Sparse (Fin 909) := [(0, (-1 / 480)), (2, (7 / 144)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 72)), (6, (1 / 288)), (7, (1 / 18)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 9)), (35, (5 / 18)), (37, (1 / 1)), (52, (2 / 9)), (56, (-1 / 3)), (73, (1 / 2)), (81, (-1 / 6)), (84, (1 / 1)), (201, (-1 / 6)), (228, (-1 / 3)), (501, (1 / 2)), (503, (1 / 1)), (541, (1 / 1)), (796, (-1 / 6))]

def value3180 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-13 / 288)), (2, (1 / 36)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 36)), (7, (2 / 9)), (12, (1 / 9)), (23, (-1 / 2)), (24, (-1 / 2)), (26, (1 / 18)), (27, (1 / 12)), (35, (1 / 9)), (47, (1 / 2)), (52, (1 / 18)), (55, (-2 / 3)), (69, (1 / 18)), (70, (1 / 18)), (125, (-1 / 2)), (126, (-1 / 3)), (197, (-1 / 6)), (538, (1 / 2)), (640, (1 / 2))]

def value3181 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-17 / 288)), (2, (7 / 144)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 18)), (7, (2 / 9)), (12, (1 / 6)), (23, (-2 / 3)), (24, (-2 / 3)), (27, (1 / 6)), (55, (-2 / 3)), (68, (1 / 24)), (125, (-1 / 2)), (126, (-1 / 3))]

def value3182 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-23 / 144)), (2, (13 / 288)), (3, (13 / 18)), (7, (1 / 9)), (12, (4 / 9)), (13, (1 / 18)), (16, (1 / 2)), (23, (-2 / 3)), (27, (1 / 24)), (47, (1 / 1)), (51, (-1 / 3)), (124, (-1 / 6)), (140, (3 / 2)), (205, (1 / 1))]

def value3183 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 32)), (2, (1 / 16)), (3, (5 / 9)), (4, (1 / 18)), (5, (-1 / 12)), (6, (1 / 288)), (7, (1 / 3)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 6)), (23, (-1 / 3)), (24, (-1 / 3)), (25, (-1 / 6)), (35, (1 / 6)), (48, (1 / 2)), (51, (-1 / 3)), (52, (1 / 9)), (54, (-1 / 2)), (56, (-1 / 3)), (64, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (100, (1 / 1)), (125, (-1 / 2)), (126, (-1 / 3)), (197, (-1 / 6)), (543, (1 / 2)), (643, (1 / 2))]

def value3184 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 12)), (2, (1 / 9)), (3, (7 / 18)), (5, (-5 / 24)), (6, (1 / 36)), (7, (2 / 9)), (12, (1 / 18)), (13, (5 / 18)), (35, (7 / 18)), (38, (1 / 2)), (52, (1 / 2)), (69, (1 / 18)), (70, (1 / 18)), (82, (1 / 18)), (128, (1 / 18)), (201, (-1 / 3)), (313, (1 / 1)), (505, (1 / 2)), (540, (1 / 2))]

def value3185 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 12)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (5 / 18)), (26, (1 / 9)), (35, (1 / 2)), (38, (1 / 2)), (52, (4 / 9)), (55, (-1 / 6)), (81, (-1 / 3)), (84, (1 / 1)), (228, (-1 / 3)), (306, (-1 / 6)), (323, (1 / 1)), (499, (1 / 2)), (540, (1 / 2)), (541, (1 / 1)), (728, (-1 / 6))]

def value3186 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-1 / 48)), (2, (5 / 96)), (3, (5 / 18)), (4, (2 / 9)), (8, (1 / 9)), (12, (1 / 18)), (15, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 2)), (25, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 3)), (33, (-1 / 6)), (48, (1 / 1)), (51, (-1 / 3)), (126, (-1 / 6)), (137, (1 / 1)), (145, (1 / 2)), (207, (1 / 1))]

def value3187 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-23 / 288)), (2, (29 / 288)), (3, (5 / 9)), (5, (-1 / 12)), (7, (2 / 9)), (8, (1 / 9)), (12, (2 / 9)), (23, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 12)), (31, (-1 / 3)), (51, (-2 / 3)), (54, (-2 / 3)), (64, (-1 / 3)), (68, (1 / 24)), (100, (1 / 1)), (125, (-1 / 2)), (126, (-1 / 3)), (238, (-1 / 3))]

def value3188 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (5 / 96)), (2, (37 / 288)), (3, (5 / 9)), (5, (-1 / 9)), (6, (1 / 96)), (7, (2 / 9)), (12, (1 / 6)), (13, (5 / 9)), (23, (-1 / 6)), (27, (1 / 24)), (35, (1 / 3)), (52, (4 / 9)), (68, (1 / 24)), (98, (1 / 2)), (125, (-1 / 2)), (126, (-1 / 3)), (237, (-1 / 6))]

def value3189 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-29 / 288)), (2, (1 / 12)), (3, (13 / 18)), (4, (1 / 6)), (5, (-1 / 18)), (6, (1 / 288)), (7, (1 / 6)), (8, (1 / 18)), (12, (5 / 18)), (13, (1 / 6)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-1 / 3)), (26, (1 / 18)), (27, (1 / 12)), (31, (-1 / 6)), (35, (1 / 6)), (51, (-5 / 6)), (52, (1 / 9)), (54, (-2 / 3)), (55, (-1 / 6)), (56, (-1 / 3)), (64, (-1 / 3)), (100, (1 / 2)), (104, (1 / 2)), (238, (-1 / 6))]

def value3190 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-53 / 288)), (2, (7 / 144)), (3, (8 / 9)), (4, (7 / 18)), (12, (1 / 3)), (13, (1 / 9)), (18, (1 / 2)), (25, (-1 / 3)), (31, (-1 / 3)), (33, (-1 / 6)), (47, (1 / 2)), (48, (1 / 2)), (50, (1 / 2)), (51, (-1 / 2)), (52, (1 / 18)), (142, (1 / 2)), (177, (1 / 1)), (209, (1 / 2))]

def value3191 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 288)), (2, (19 / 288)), (3, (1 / 2)), (4, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (7, (2 / 9)), (8, (1 / 18)), (10, (-1 / 6)), (11, (1 / 18)), (12, (1 / 9)), (13, (5 / 18)), (26, (1 / 9)), (33, (-1 / 6)), (35, (1 / 2)), (41, (1 / 2)), (52, (7 / 18)), (59, (-1 / 6)), (73, (1 / 2)), (81, (-1 / 6)), (82, (1 / 18)), (84, (1 / 2)), (128, (1 / 18)), (201, (-1 / 6)), (228, (-1 / 3)), (306, (-1 / 6)), (313, (1 / 2)), (324, (1 / 1)), (502, (1 / 2)), (517, (1 / 2)), (545, (1 / 2)), (721, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2240 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 16)), (2, (-1 / 48)), (3, (-1 / 18)), (12, (-1 / 18)), (27, (-1 / 24)), (51, (1 / 6)), (205, (-1 / 2)), (208, (-1 / 2))]

def value2241 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (7 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (12, (-1 / 18)), (47, (-1 / 2)), (48, (-1 / 2)), (51, (1 / 6)), (191, (-1 / 2))]

def value2242 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 72)), (3, (-1 / 9)), (5, (1 / 36)), (13, (-1 / 9)), (52, (-1 / 9)), (126, (1 / 6)), (144, (-1 / 2))]

def value2243 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 96)), (2, (1 / 144)), (3, (-1 / 6)), (4, (-1 / 18)), (13, (-1 / 6)), (26, (-1 / 9)), (33, (1 / 6)), (35, (-1 / 18)), (55, (1 / 6)), (63, (1 / 6)), (143, (-1 / 2))]

def value2244 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 288)), (2, (1 / 288)), (3, (-1 / 6)), (13, (-2 / 9)), (33, (1 / 6)), (52, (-1 / 18)), (63, (1 / 6)), (237, (1 / 6))]

def value2245 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 72)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (13, (-2 / 9)), (35, (-1 / 9)), (52, (-1 / 6)), (63, (1 / 6)), (123, (1 / 6)), (306, (1 / 6))]

def value2246 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (-1 / 9)), (13, (-2 / 9)), (231, (-1 / 2)), (760, (-1 / 2))]

def value2247 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 288)), (5, (5 / 72)), (6, (-5 / 288)), (7, (-1 / 9)), (11, (-1 / 9)), (35, (-5 / 18)), (70, (-1 / 18)), (228, (1 / 6)), (259, (1 / 6)), (721, (1 / 6))]

def value2248 : Sparse (Fin 909) := [(2, (11 / 288)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (11, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (228, (1 / 6)), (728, (1 / 6)), (764, (-1 / 2))]

def value2249 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 144)), (35, (-1 / 18)), (52, (-1 / 6)), (228, (1 / 6)), (322, (-1 / 2)), (517, (-1 / 2))]

def value2250 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 24)), (6, (-1 / 288)), (7, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 9)), (85, (-1 / 2)), (228, (1 / 3)), (315, (-1 / 2))]

def value2251 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 32)), (2, (-1 / 72)), (3, (-2 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (51, (1 / 6)), (52, (-1 / 18)), (103, (-1 / 2)), (123, (1 / 6))]

def value2252 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-1 / 32)), (5, (1 / 18)), (6, (-1 / 288)), (8, (-1 / 18)), (52, (-1 / 18)), (85, (-1 / 2)), (329, (-1 / 2)), (794, (-1 / 2))]

def value2253 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 288)), (2, (-7 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (35, (-1 / 18)), (52, (-1 / 6)), (228, (1 / 6)), (329, (-1 / 2)), (541, (-1 / 2))]

def value2254 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 72)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 9)), (26, (-1 / 18)), (35, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 9)), (56, (1 / 6)), (103, (-1 / 2))]

def value2255 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 144)), (2, (1 / 144)), (3, (-1 / 2)), (4, (-1 / 3)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-5 / 18)), (35, (-1 / 9)), (56, (1 / 3))]

def value2256 : Sparse (Fin 909) := [(1, (5 / 288)), (3, (-1 / 3)), (4, (-1 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (7, (-1 / 9)), (11, (-1 / 9)), (26, (-5 / 18)), (35, (-5 / 18)), (52, (-1 / 18)), (81, (1 / 6)), (228, (1 / 3))]

def value2257 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (6, (-1 / 288)), (11, (-1 / 9)), (13, (-1 / 18)), (26, (-5 / 18)), (35, (-2 / 9)), (56, (1 / 6)), (228, (1 / 6)), (546, (-1 / 2))]

def value2258 : Sparse (Fin 909) := [(1, (1 / 72)), (3, (-1 / 18)), (5, (1 / 72)), (26, (-1 / 18)), (54, (1 / 6)), (55, (1 / 6)), (77, (-1 / 2)), (228, (1 / 3)), (737, (-1 / 2))]

def value2259 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 288)), (3, (-1 / 6)), (4, (-1 / 9)), (26, (-1 / 6)), (43, (-1 / 2)), (546, (-1 / 2)), (745, (-1 / 2))]

def value2260 : Sparse (Fin 909) := [(43, (-1 / 2)), (103, (-1 / 2)), (546, (-1 / 2)), (737, (-1 / 2))]

def value2261 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (1 / 96)), (3, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 9)), (54, (1 / 6)), (97, (-1 / 2)), (217, (-1 / 2))]

def value2262 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (1 / 144)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (13, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (56, (1 / 6)), (197, (1 / 6)), (216, (-1 / 2))]

def value2263 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-1 / 18)), (39, (-1 / 2)), (42, (-1 / 2)), (99, (-1 / 2))]

def value2264 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 72)), (3, (-2 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 6)), (33, (1 / 6)), (35, (-1 / 18)), (123, (1 / 6)), (217, (-1 / 2))]

def value2265 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (1 / 288)), (3, (-2 / 9)), (4, (-1 / 18)), (13, (-1 / 9)), (25, (1 / 6)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6)), (217, (-1 / 2))]

def value2266 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 144)), (2, (-1 / 48)), (3, (-1 / 6)), (4, (-1 / 18)), (13, (-1 / 9)), (39, (-1 / 2)), (42, (-1 / 2)), (56, (1 / 6))]

def value2267 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 36)), (2, (1 / 32)), (3, (-1 / 9)), (13, (-1 / 6)), (26, (-1 / 9)), (35, (-1 / 6)), (54, (1 / 3)), (56, (1 / 6))]

def value2268 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (5 / 288)), (3, (-1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (35, (-1 / 9)), (55, (1 / 6)), (63, (1 / 6)), (70, (-1 / 18)), (196, (1 / 6)), (197, (1 / 6)), (643, (-1 / 2))]

def value2269 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 36)), (6, (5 / 144)), (11, (-1 / 9)), (35, (-1 / 6)), (70, (-1 / 18)), (728, (1 / 6)), (783, (-1 / 2))]

def value2270 : Sparse (Fin 909) := [(36, (-1 / 2)), (312, (-1 / 2)), (498, (-1 / 2)), (783, (-1 / 2))]

def value2271 : Sparse (Fin 909) := [(37, (-1 / 2)), (83, (-1 / 2)), (501, (-1 / 2)), (784, (-1 / 2))]

def value2272 : Sparse (Fin 909) := [(1, (1 / 18)), (2, (-1 / 72)), (3, (-1 / 6)), (7, (-1 / 9)), (12, (-1 / 18)), (23, (1 / 3)), (24, (1 / 3)), (27, (-1 / 24)), (55, (1 / 6)), (124, (1 / 6)), (197, (1 / 6))]

def value2273 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-1 / 288)), (23, (1 / 6)), (25, (1 / 6)), (48, (-1 / 2)), (137, (-1 / 2)), (230, (-1 / 2))]

def value2274 : Sparse (Fin 909) := [(1, (1 / 288)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 18)), (35, (-1 / 18)), (83, (-1 / 2)), (228, (1 / 6)), (312, (-1 / 2)), (784, (-1 / 2))]

def value2275 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 96)), (3, (-1 / 6)), (5, (1 / 36)), (6, (-1 / 288)), (7, (-1 / 9)), (26, (-1 / 6)), (35, (-1 / 9)), (123, (1 / 6)), (124, (1 / 6)), (197, (1 / 6))]

def value2276 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (5 / 288)), (5, (1 / 72)), (6, (-1 / 96)), (7, (-1 / 18)), (35, (-1 / 18)), (228, (1 / 6)), (312, (-1 / 2)), (794, (-1 / 2))]

def value2277 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 48)), (3, (-1 / 18)), (5, (1 / 72)), (7, (-1 / 18)), (24, (1 / 3)), (27, (-1 / 12)), (68, (-1 / 24)), (124, (1 / 6)), (126, (1 / 3)), (197, (1 / 3))]

def value2278 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (33, (1 / 3)), (55, (1 / 3)), (306, (1 / 3)), (312, (-1 / 2)), (721, (1 / 6)), (728, (1 / 6))]

def value2279 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 144)), (3, (-1 / 18)), (4, (-1 / 18)), (27, (-1 / 24)), (55, (1 / 6)), (126, (1 / 6)), (197, (1 / 6))]

def value2280 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 6)), (33, (1 / 6)), (197, (1 / 6)), (306, (1 / 6)), (728, (1 / 6))]

def value2281 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 36)), (2, (-1 / 288)), (3, (-1 / 18)), (4, (-1 / 18)), (15, (-1 / 2)), (24, (1 / 6)), (137, (-1 / 2)), (205, (-1 / 2))]

def value2282 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (-1 / 9)), (4, (-1 / 18)), (12, (-1 / 18)), (23, (1 / 6)), (24, (1 / 6)), (55, (1 / 3)), (290, (-1 / 2)), (299, (-1 / 2))]

def value2283 : Sparse (Fin 909) := [(37, (-1 / 2)), (517, (-1 / 2)), (541, (-1 / 2)), (784, (-1 / 2))]

def value2284 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 288)), (3, (-1 / 9)), (4, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (24, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 18)), (52, (-1 / 18)), (99, (-1 / 2)), (126, (1 / 6)), (197, (1 / 6))]

def value2285 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (-1 / 96)), (3, (-2 / 9)), (4, (-1 / 9)), (26, (-1 / 9)), (31, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 18)), (99, (-1 / 2)), (123, (1 / 6)), (237, (1 / 6))]

def value2286 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (2, (1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (11, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (55, (1 / 6)), (306, (1 / 6)), (728, (1 / 6)), (794, (-1 / 2))]

def value2287 : Sparse (Fin 909) := [(40, (-1 / 2)), (760, (-1 / 2)), (794, (-1 / 1))]

def value2288 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (24, (1 / 3)), (55, (1 / 3)), (126, (1 / 6)), (197, (1 / 3)), (290, (-1 / 2)), (728, (1 / 6))]

def value2289 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (11 / 288)), (2, (1 / 144)), (3, (-2 / 9)), (4, (-1 / 18)), (7, (-1 / 18)), (12, (-1 / 9)), (13, (-1 / 18)), (23, (1 / 3)), (24, (1 / 6)), (25, (1 / 6)), (35, (-1 / 18)), (55, (1 / 3)), (63, (1 / 6))]

def value2290 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (5 / 288)), (2, (1 / 144)), (3, (-1 / 9)), (7, (-1 / 18)), (12, (-1 / 18)), (13, (-1 / 18)), (23, (1 / 6)), (35, (-1 / 18)), (55, (1 / 6)), (124, (1 / 6)), (196, (1 / 6)), (197, (1 / 6)), (290, (-1 / 2)), (728, (1 / 6))]

def value2291 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (19 / 288)), (3, (-1 / 3)), (4, (-2 / 9)), (25, (1 / 3)), (26, (-2 / 9)), (31, (1 / 6)), (35, (-1 / 18)), (123, (1 / 6))]

def value2292 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 72)), (2, (-1 / 288)), (3, (-1 / 6)), (12, (-1 / 18)), (26, (-1 / 9)), (44, (-1 / 2)), (55, (1 / 6)), (108, (-1 / 2))]

def value2293 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (13 / 288)), (2, (5 / 144)), (3, (-1 / 9)), (13, (-1 / 9)), (26, (-1 / 6)), (35, (-1 / 6)), (55, (1 / 6)), (63, (1 / 6)), (123, (1 / 6))]

def value2294 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-5 / 32)), (2, (-5 / 32)), (3, (-1 / 3)), (5, (1 / 3)), (6, (-1 / 32)), (7, (-1 / 3)), (8, (-1 / 3)), (11, (-1 / 6)), (26, (-1 / 6)), (33, (1 / 2)), (35, (-1 / 2)), (52, (-1 / 2)), (59, (1 / 2)), (81, (1 / 1)), (228, (1 / 1)), (490, (1 / 1)), (721, (1 / 2))]

def value2295 : Sparse (Fin 909) := [(0, (-1 / 30)), (1, (7 / 16)), (2, (-7 / 48)), (3, (-7 / 6)), (4, (-2 / 3)), (12, (-1 / 3)), (25, (1 / 2)), (26, (-1 / 6)), (31, (1 / 1)), (33, (1 / 2))]

def value2296 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (11 / 96)), (2, (1 / 12)), (3, (-4 / 3)), (4, (-1 / 2)), (5, (1 / 24)), (6, (-1 / 96)), (11, (-1 / 6)), (12, (-1 / 3)), (13, (-5 / 6)), (26, (-2 / 3)), (35, (-5 / 6)), (52, (-1 / 6)), (54, (1 / 2)), (56, (1 / 1)), (228, (1 / 2))]

def value2297 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (7 / 32)), (2, (7 / 96)), (3, (-3 / 2)), (4, (-2 / 3)), (12, (-1 / 3)), (13, (-5 / 6)), (26, (-2 / 3)), (35, (-1 / 2)), (54, (1 / 2)), (56, (1 / 1))]

def value2298 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 16)), (2, (1 / 16)), (3, (-2 / 3)), (4, (-1 / 6)), (5, (1 / 12)), (6, (-1 / 48)), (7, (-1 / 6)), (11, (-1 / 6)), (13, (-1 / 6)), (25, (1 / 2)), (26, (-2 / 3)), (35, (-2 / 3)), (54, (3 / 2)), (56, (1 / 2)), (226, (1 / 2)), (228, (1 / 2))]

def value2299 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (5 / 16)), (2, (-1 / 48)), (3, (-7 / 6)), (4, (-2 / 3)), (7, (-1 / 6)), (12, (-1 / 3)), (13, (-1 / 6)), (24, (1 / 2)), (26, (-1 / 3)), (35, (-1 / 6)), (56, (1 / 2))]

def value2300 : Sparse (Fin 909) := [(1, (5 / 48)), (2, (1 / 48)), (3, (-3 / 2)), (4, (-2 / 3)), (7, (-1 / 6)), (12, (-1 / 3)), (23, (1 / 2)), (25, (1 / 1)), (26, (-2 / 3)), (35, (-1 / 6)), (54, (1 / 2))]

def value2301 : Sparse (Fin 909) := [(0, (-1 / 32)), (1, (25 / 48)), (2, (-5 / 96)), (3, (-3 / 2)), (4, (-1 / 1)), (12, (-2 / 3)), (25, (1 / 2)), (26, (-1 / 3))]

def value2302 : Sparse (Fin 909) := [(1, (1 / 12)), (2, (-7 / 96)), (3, (-3 / 2)), (4, (-1 / 2)), (5, (1 / 6)), (6, (-1 / 32)), (7, (-1 / 2)), (11, (-1 / 2)), (26, (-1 / 1)), (35, (-4 / 3)), (52, (-1 / 2)), (228, (3 / 2))]

def value2303 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (19 / 48)), (2, (-5 / 48)), (3, (-2 / 1)), (4, (-1 / 1)), (5, (1 / 24)), (7, (-1 / 2)), (26, (-1 / 1)), (35, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value2304 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-3 / 8)), (2, (-1 / 48)), (3, (-2 / 3)), (12, (-2 / 3)), (25, (1 / 2))]

def value2305 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 4)), (2, (-1 / 24)), (3, (-1 / 1)), (4, (-1 / 3)), (12, (-1 / 6)), (26, (-1 / 3))]

def value2306 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (3 / 8)), (2, (-1 / 48)), (3, (-1 / 3)), (4, (-2 / 3)), (12, (-1 / 6))]

def value2307 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-1 / 72)), (3, (-1 / 18)), (5, (1 / 24)), (13, (-1 / 9)), (35, (-1 / 18)), (52, (-1 / 9)), (56, (1 / 6)), (82, (-1 / 18)), (128, (-1 / 18)), (262, (1 / 6)), (796, (1 / 6)), (798, (-1 / 2))]

def value2308 : Sparse (Fin 909) := [(42, (-1 / 2)), (328, (-1 / 2)), (506, (-1 / 2)), (798, (-1 / 2))]

def value2309 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 144)), (6, (-1 / 288)), (7, (-1 / 9)), (35, (-1 / 9)), (54, (1 / 6)), (199, (1 / 6)), (286, (-1 / 2)), (506, (-1 / 2))]

def value2310 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 288)), (2, (-5 / 288)), (5, (1 / 36)), (6, (-1 / 288)), (8, (-1 / 9)), (56, (1 / 6)), (201, (1 / 6)), (288, (-1 / 2)), (500, (-1 / 2))]

def value2311 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 32)), (2, (-1 / 32)), (5, (1 / 18)), (6, (-1 / 288)), (8, (-1 / 18)), (52, (-1 / 18)), (99, (-1 / 2)), (500, (-1 / 2)), (798, (-1 / 2))]

def value2312 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (11 / 288)), (5, (1 / 18)), (26, (-1 / 18)), (35, (-1 / 9)), (71, (-1 / 18)), (82, (-1 / 18)), (197, (1 / 6)), (764, (-1 / 2)), (796, (1 / 6))]

def value2313 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (7, (-1 / 18)), (13, (-1 / 18)), (35, (-1 / 9)), (56, (1 / 6)), (82, (-1 / 18)), (228, (1 / 6)), (794, (-1 / 2)), (796, (1 / 6))]

def value2314 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-1 / 72)), (5, (1 / 36)), (8, (1 / 18)), (75, (-1 / 2)), (508, (-1 / 1))]

def value2315 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (7 / 144)), (2, (-5 / 288)), (3, (-2 / 9)), (4, (-1 / 9)), (12, (-1 / 18)), (13, (-1 / 18)), (26, (-1 / 18)), (40, (-1 / 2)), (56, (1 / 6))]

def value2316 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 288)), (2, (-1 / 144)), (3, (-1 / 18)), (7, (-1 / 6)), (8, (-1 / 9)), (10, (1 / 6)), (35, (-1 / 18)), (501, (-1 / 2)), (508, (-1 / 2))]

def value2317 : Sparse (Fin 909) := [(40, (-1 / 2)), (85, (-1 / 2)), (508, (-1 / 2)), (794, (-1 / 2))]

def value2318 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (1 / 16)), (2, (-1 / 288)), (3, (-5 / 18)), (4, (-1 / 3)), (26, (-1 / 9)), (40, (-1 / 2)), (56, (1 / 6))]

def value2319 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 288)), (2, (1 / 72)), (3, (-5 / 18)), (4, (-1 / 9)), (11, (-1 / 18)), (13, (-1 / 9)), (26, (-2 / 9)), (35, (-5 / 18)), (52, (-1 / 18)), (56, (1 / 3)), (262, (1 / 6)), (796, (1 / 6))]

def value2320 : Sparse (Fin 909) := [(1, (11 / 288)), (2, (1 / 96)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 9)), (35, (-1 / 18)), (54, (1 / 6)), (103, (-1 / 2)), (228, (1 / 6)), (286, (-1 / 2))]

def value2321 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 144)), (2, (-1 / 96)), (3, (-1 / 9)), (5, (1 / 36)), (6, (-1 / 144)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 9)), (51, (1 / 6)), (52, (-1 / 9)), (82, (-1 / 18)), (128, (-1 / 18)), (262, (1 / 6)), (309, (1 / 6)), (328, (-1 / 2))]

def value2322 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-11 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (8, (-1 / 18)), (13, (-1 / 18)), (52, (-1 / 6)), (71, (-1 / 18)), (126, (1 / 6)), (128, (-1 / 18)), (262, (1 / 6)), (329, (-1 / 2))]

def value2323 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-5 / 144)), (3, (-2 / 9)), (5, (1 / 72)), (6, (-1 / 288)), (12, (-1 / 18)), (13, (-1 / 6)), (35, (-1 / 18)), (51, (1 / 3)), (52, (-2 / 9)), (262, (1 / 6)), (309, (1 / 6))]

def value2324 : Sparse (Fin 909) := [(1, (-7 / 288)), (2, (5 / 288)), (5, (1 / 18)), (9, (1 / 72)), (13, (-1 / 6)), (35, (-2 / 9)), (68, (-1 / 24)), (82, (-1 / 9)), (309, (1 / 6)), (728, (1 / 6))]

def value2325 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (5 / 288)), (2, (-1 / 144)), (3, (-1 / 9)), (5, (1 / 24)), (6, (-1 / 144)), (7, (-1 / 18)), (8, (-1 / 18)), (26, (-1 / 18)), (35, (-1 / 18)), (71, (-1 / 18)), (197, (1 / 6)), (236, (1 / 6)), (810, (-1 / 2))]

def value2326 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (10, (1 / 6)), (12, (-1 / 18)), (13, (-1 / 18)), (27, (-1 / 24)), (55, (1 / 3)), (538, (-1 / 2)), (811, (-1 / 2))]

def value2327 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (-13 / 288)), (3, (-1 / 18)), (5, (1 / 18)), (6, (-1 / 288)), (7, (-1 / 18)), (8, (-1 / 9)), (71, (-1 / 18)), (126, (1 / 6)), (236, (1 / 6)), (811, (-1 / 2))]

def value2328 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 144)), (2, (-1 / 288)), (5, (1 / 72)), (7, (-1 / 18)), (8, (-1 / 18)), (69, (-1 / 18)), (71, (-1 / 18)), (124, (1 / 6)), (126, (1 / 3)), (236, (1 / 6)), (290, (-1 / 2))]

def value2329 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 144)), (2, (1 / 288)), (5, (1 / 72)), (6, (-1 / 288)), (27, (-1 / 12)), (30, (1 / 3)), (68, (-1 / 24)), (124, (1 / 6)), (236, (2 / 3))]

def value2330 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (-1 / 48)), (5, (1 / 36)), (6, (-1 / 144)), (23, (1 / 6)), (27, (-1 / 24)), (68, (-1 / 24)), (124, (1 / 3)), (196, (1 / 6)), (236, (1 / 3))]

def value2331 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 96)), (3, (-1 / 18)), (4, (-1 / 18)), (31, (1 / 6)), (51, (1 / 6)), (106, (-1 / 2)), (538, (-1 / 2)), (812, (-1 / 2))]

def value2332 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 24)), (2, (-5 / 144)), (3, (-1 / 18)), (52, (-1 / 9)), (55, (1 / 6)), (237, (1 / 3)), (308, (1 / 6)), (640, (-1 / 2))]

def value2333 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 288)), (2, (-7 / 288)), (5, (1 / 24)), (6, (-1 / 288)), (27, (-1 / 24)), (33, (1 / 6)), (51, (1 / 6)), (55, (1 / 6)), (306, (1 / 6)), (308, (1 / 6)), (811, (-1 / 2))]

def value2334 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (2, (-1 / 144)), (8, (-1 / 18)), (24, (1 / 6)), (30, (1 / 6)), (49, (-1 / 2)), (811, (-1 / 2)), (812, (-1 / 2))]

def value2335 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 72)), (2, (-5 / 288)), (5, (1 / 72)), (27, (-1 / 12)), (299, (-1 / 2)), (751, (-1 / 2)), (812, (-1 / 2))]

def value2336 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 48)), (2, (-1 / 144)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 288)), (24, (1 / 6)), (27, (-1 / 12)), (55, (1 / 3)), (68, (-1 / 24)), (197, (1 / 6)), (237, (1 / 6))]

def value2337 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (-1 / 36)), (8, (-1 / 9)), (24, (1 / 3)), (27, (-1 / 12)), (30, (1 / 3)), (126, (1 / 6)), (236, (1 / 6))]

def value2338 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 32)), (2, (-17 / 288)), (5, (1 / 18)), (27, (-5 / 24)), (30, (1 / 6)), (68, (-1 / 24)), (236, (1 / 6))]

def value2339 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 32)), (2, (-1 / 36)), (5, (1 / 72)), (24, (1 / 3)), (27, (-1 / 12)), (106, (-1 / 2)), (126, (1 / 3))]

def value2340 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (23, (1 / 6)), (27, (1 / 8)), (68, (-1 / 24)), (124, (1 / 6))]

def value2341 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 36)), (2, (-1 / 144)), (25, (1 / 6)), (27, (-1 / 24)), (63, (1 / 6)), (124, (1 / 6)), (196, (1 / 6))]

def value2342 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (1 / 288)), (6, (-1 / 288)), (30, (1 / 6)), (31, (1 / 6)), (68, (-1 / 24)), (236, (1 / 6)), (237, (1 / 6))]

def value2343 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 48)), (2, (-1 / 72)), (27, (-1 / 12)), (236, (1 / 3))]

def value2344 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 288)), (2, (-1 / 144)), (5, (1 / 72)), (23, (1 / 6)), (27, (-1 / 12)), (30, (1 / 6)), (105, (-1 / 2)), (124, (1 / 6)), (236, (1 / 6))]

def value2345 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 72)), (2, (-1 / 72)), (23, (1 / 2)), (25, (1 / 2)), (27, (-1 / 24)), (63, (1 / 3))]

def value2346 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 18)), (2, (-1 / 72)), (27, (-1 / 12)), (30, (1 / 6)), (31, (1 / 3)), (105, (-1 / 2)), (237, (1 / 6))]

def value2347 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (23, (1 / 6)), (25, (1 / 6)), (27, (-1 / 24)), (31, (1 / 6)), (63, (1 / 6)), (105, (-1 / 2)), (237, (1 / 6))]

def value2348 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 48)), (2, (-7 / 288)), (5, (1 / 24)), (6, (-1 / 96)), (33, (1 / 6)), (51, (1 / 6)), (259, (1 / 6)), (306, (1 / 6)), (308, (1 / 6)), (315, (-1 / 2)), (721, (1 / 6))]

def value2349 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 48)), (2, (-7 / 288)), (3, (-1 / 18)), (5, (1 / 36)), (6, (-1 / 144)), (31, (1 / 6)), (33, (1 / 6)), (35, (-1 / 18)), (52, (-1 / 9)), (123, (1 / 6)), (237, (1 / 6)), (306, (1 / 6)), (315, (-1 / 2)), (721, (1 / 6))]

def value2350 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (3, (-1 / 9)), (5, (1 / 72)), (7, (-1 / 18)), (26, (-1 / 18)), (33, (1 / 6)), (51, (1 / 6)), (123, (1 / 6)), (124, (1 / 6)), (137, (-1 / 2))]

def value2351 : Sparse (Fin 909) := [(1, (-1 / 12)), (23, (1 / 3)), (25, (1 / 6)), (27, (-1 / 12)), (124, (1 / 6)), (230, (-1 / 2))]

def value2352 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-5 / 144)), (2, (-1 / 288)), (14, (-1 / 2)), (23, (1 / 6)), (25, (1 / 6)), (129, (-1 / 2)), (230, (-1 / 2))]

def value2353 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 288)), (2, (-1 / 288)), (5, (1 / 72)), (23, (1 / 6)), (25, (1 / 6)), (27, (-1 / 24)), (31, (1 / 6)), (123, (1 / 6)), (124, (1 / 6)), (203, (-1 / 2))]

def value2354 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 144)), (2, (-1 / 144)), (17, (-1 / 2)), (30, (1 / 6)), (203, (-1 / 1))]

def value2355 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (27, (-1 / 24)), (108, (-1 / 2)), (203, (-1 / 2)), (230, (-1 / 2))]

def value2356 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (1 / 36)), (63, (1 / 6)), (123, (1 / 3)), (124, (1 / 6)), (129, (-1 / 2))]

def value2357 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 144)), (2, (1 / 288)), (5, (1 / 72)), (6, (-1 / 288)), (27, (-1 / 12)), (31, (1 / 3)), (68, (-1 / 24)), (123, (1 / 3)), (124, (1 / 6)), (237, (1 / 3))]

def value2358 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 72)), (2, (-1 / 144)), (23, (1 / 3)), (63, (1 / 3))]

def value2359 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (13 / 288)), (2, (-1 / 144)), (25, (1 / 6)), (27, (-1 / 24)), (123, (1 / 6)), (237, (1 / 6))]

def value2360 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (7 / 96)), (2, (-1 / 288)), (25, (1 / 3)), (31, (1 / 2)), (108, (-1 / 2)), (123, (1 / 6))]

def value2361 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 288)), (2, (1 / 72)), (23, (1 / 6)), (25, (1 / 3)), (31, (1 / 6)), (63, (1 / 6)), (108, (-1 / 2)), (123, (1 / 6))]

def value2362 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (5 / 72)), (17, (-1 / 2)), (25, (1 / 3)), (31, (1 / 3)), (231, (-1 / 2))]

def value2363 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (3, (-1 / 18)), (5, (1 / 72)), (35, (-1 / 18)), (52, (-1 / 9)), (89, (-1 / 2)), (228, (1 / 6)), (507, (-1 / 2)), (540, (-1 / 2))]

def value2364 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 24)), (5, (1 / 72)), (6, (1 / 72)), (54, (1 / 3)), (259, (1 / 6)), (721, (1 / 6)), (723, (1 / 3)), (764, (-1 / 2))]

def value2365 : Sparse (Fin 909) := [(39, (-1 / 2)), (315, (-1 / 2)), (507, (-1 / 2)), (764, (-1 / 2))]

def value2366 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 288)), (3, (-1 / 18)), (5, (1 / 72)), (6, (-1 / 288)), (11, (-1 / 18)), (25, (1 / 6)), (26, (-1 / 18)), (35, (-1 / 9)), (52, (-1 / 18)), (54, (1 / 6)), (123, (1 / 6)), (226, (1 / 6)), (507, (-1 / 2)), (721, (1 / 6)), (723, (1 / 6))]

def value2367 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 144)), (5, (-1 / 18)), (6, (-1 / 288)), (282, (-1 / 2)), (498, (-1 / 2)), (507, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryRow88 : Integer.Sparse (Fin 909) := [(0, 6), (1, -189), (2, 83), (3, 832), (4, 368), (5, -28), (6, 2), (7, 112), (8, 16), (12, 320), (13, 96), (23, -48), (24, -48), (25, -336), (26, 128), (31, -336), (33, -336), (35, 80), (43, 288), (46, 288), (50, 144), (51, -96), (52, 64), (55, -96), (81, -96), (95, 144), (104, 144), (113, 288), (122, 288)]

def boundaryRow89 : Integer.Sparse (Fin 909) := [(0, -1), (1, -56), (2, 56), (3, 464), (4, 80), (5, -40), (6, 1), (7, 80), (8, 80), (10, -72), (12, 184), (13, 192), (24, -48), (26, 32), (35, 32), (38, 72), (40, 144), (51, -48), (52, 48), (55, -72), (59, -144), (72, 72), (75, 144), (94, 144), (95, 288), (102, 288), (199, -24)]

def boundaryRow90 : Integer.Sparse (Fin 909) := [(0, 31), (1, -362), (2, 90), (3, 768), (4, 704), (5, -20), (6, 1), (7, 32), (8, 32), (12, 144), (24, -96), (25, -240), (26, 160), (31, -768), (35, 32), (43, 288), (44, 576), (52, 32), (55, -96), (95, 288), (113, 144)]

def boundaryRow91 : Integer.Sparse (Fin 909) := [(0, 68), (1, -1405), (2, 540), (3, 5040), (4, 2240), (5, -180), (6, 5), (7, 880), (8, 160), (10, -240), (12, 2480), (13, 160), (23, -2160), (24, -1440), (25, -480), (26, 640), (27, 420), (31, -1440), (35, 240), (43, 2880), (52, 160), (55, -1200), (79, 720), (95, 1440), (113, 1440)]

def boundaryRow92 : Integer.Sparse (Fin 909) := [(0, 54), (1, -935), (2, 310), (3, 3280), (4, 1480), (5, -140), (6, 5), (7, 360), (8, 360), (12, 1080), (23, -480), (24, -120), (26, 720), (27, 30), (31, -240), (35, 80), (43, 720), (45, 1440), (51, -600), (55, -240), (56, -480), (77, 360), (105, 720), (107, 720), (228, -120)]

def boundaryRow93 : Integer.Sparse (Fin 909) := [(0, 4), (1, -875), (2, 605), (3, 5680), (4, 640), (5, -420), (6, 20), (7, 880), (8, 640), (10, -720), (12, 3120), (13, 3840), (23, -480), (26, 320), (33, -1920), (35, 800), (36, 720), (38, 1440), (40, 1440), (52, 640), (54, -1200), (55, -720), (59, -960), (72, 720), (75, 1440), (199, -240)]

def boundaryRow94 : Integer.Sparse (Fin 909) := [(0, 8), (1, -1045), (2, 155), (3, 6480), (4, 1920), (10, -720), (12, 3200), (13, 2800), (23, -480), (24, -960), (25, -720), (27, 60), (33, -1920), (50, 1440), (55, -1920), (59, -720), (79, 720), (80, 1440), (94, 720), (101, 1440)]

def boundaryRow95 : Integer.Sparse (Fin 909) := [(0, -7), (1, -515), (2, 435), (3, 4560), (4, 800), (5, -100), (6, 5), (7, 480), (12, 3200), (13, 3600), (25, -240), (26, 160), (33, -960), (35, 800), (41, 1440), (52, 640), (59, -720), (73, 720), (75, 1440), (94, 720), (101, 1440), (201, -720)]

def boundaryRow96 : Integer.Sparse (Fin 909) := [(0, -22), (1, -465), (2, 365), (3, 4880), (4, 320), (5, -180), (7, 720), (8, 320), (10, -240), (12, 2800), (13, 3920), (23, -720), (25, -240), (27, 180), (33, -960), (35, 320), (38, 1440), (51, -1920), (54, -1920), (55, -480), (59, -1680), (72, 720), (74, 1440), (94, 720), (101, 1440), (199, -720)]

def boundaryRow97 : Integer.Sparse (Fin 909) := [(0, 6), (1, -140), (2, 225), (3, 2560), (4, 800), (5, -260), (6, 15), (7, 1360), (8, 160), (12, 1600), (13, 1040), (23, -480), (25, -960), (26, 720), (35, 1200), (38, 1440), (41, 720), (43, 1440), (52, 560), (54, -720), (84, 720), (97, 1440), (98, 1440), (228, -240)]

def boundaryRow98 : Integer.Sparse (Fin 909) := [(0, 39), (1, -385), (2, 615), (3, 3600), (4, 960), (5, -740), (6, 65), (7, 720), (8, 1120), (12, 560), (13, 240), (23, -240), (26, 640), (31, -720), (33, -480), (35, 560), (44, 1440), (51, -1440), (52, 880), (54, -960), (81, -480), (95, 720), (99, 1440), (100, 1440)]

def boundaryRow99 : Integer.Sparse (Fin 909) := [(0, 24), (1, -795), (2, 495), (3, 4320), (4, 2000), (5, -220), (6, 10), (7, 800), (8, 160), (12, 1120), (13, 960), (25, -960), (26, 1280), (31, -1200), (33, -960), (35, 720), (38, 720), (39, 1440), (41, 1440), (46, 1440), (51, -480), (52, 640), (54, -720), (81, -480), (84, 720), (85, 1440), (95, 720), (103, 1440), (228, -720)]

end MUB6.Certificate.PairSemantics

end OAI
end


