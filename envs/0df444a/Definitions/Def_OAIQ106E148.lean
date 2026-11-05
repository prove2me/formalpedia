-- Prove2me | Definitions.Def_OAIQ106E148
-- name    : OAIQ106E148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:34:45.783607+00:00
-- url     : https://prove2.me/theorems/a1bae2b9-358f-41e8-9975-fe3c0c920045
-- title:
--   Definitions bundle OAIQ106E148 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3033 declarations of OpenAI's Lean: 3033 definitions. The definitions and types are `OAI.MUB6.Certificate.PairSemantics.value1406`, `OAI.MUB6.Certificate.PairSemantics.value1407`, `OAI.MUB6.Certificate.PairSemantics.value1408`, `OAI.MUB6.Certificate.PairSemantics.value1409`, `OAI.MUB6.Certificate.PairSemantics.value1410`, `OAI.MUB6.Certificate.PairSemantics.value1411`, `OAI.MUB6.Certificate.PairSemantics.value1412`, `OAI.MUB6.Certificate.PairSemantics.value1413`, `OAI.MUB6.Certificate.PairSemantics.value1414`, `OAI.MUB6.Certificate.PairSemantics.value1415`, `OAI.MUB6.Certificate.PairSemantics.value1416`, `OAI.MUB6.Certificate.PairSemantics.value1417`, `OAI.MUB6.Certificate.PairSemantics.value1418`, `OAI.MUB6.Certificate.PairSemantics.value1419`, `OAI.MUB6.Certificate.PairSemantics.value142`, `OAI.MUB6.Certificate.PairSemantics.value1420`, `OAI.MUB6.Certificate.PairSemantics.value1421`, `OAI.MUB6.Certificate.PairSemantics.value1422`, `OAI.MUB6.Certificate.PairSemantics.value1423`, `OAI.MUB6.Certificate.PairSemantics.value1424`, `OAI.MUB6.Certificate.PairSemantics.value1425`, `OAI.MUB6.Certificate.PairSemantics.value1426`, `OAI.MUB6.Certificate.PairSemantics.value1427`, `OAI.MUB6.Certificate.PairSemantics.value1428`, `OAI.MUB6.Certificate.PairSemantics.value1429`, `OAI.MUB6.Certificate.PairSemantics.value143`, `OAI.MUB6.Certificate.PairSemantics.value1430`, `OAI.MUB6.Certificate.PairSemantics.value1431`, `OAI.MUB6.Certificate.PairSemantics.value1432`, `OAI.MUB6.Certificate.PairSemantics.value1433`, `OAI.MUB6.Certificate.PairSemantics.value1434`, `OAI.MUB6.Certificate.PairSemantics.value1435`, `OAI.MUB6.Certificate.PairSemantics.value1436`, `OAI.MUB6.Certificate.PairSemantics.value1437`, `OAI.MUB6.Certificate.PairSemantics.value1438`, `OAI.MUB6.Certificate.PairSemantics.value1439`, `OAI.MUB6.Certificate.PairSemantics.value144`, `OAI.MUB6.Certificate.PairSemantics.value1440`, `OAI.MUB6.Certificate.PairSemantics.value1441`, `OAI.MUB6.Certificate.PairSemantics.value1442` and 2993 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_PairSemantics_Values0`, `MutuallyUnbiased_PairSemantics_Values1`, `MutuallyUnbiased_PairSemantics_Values10`, `MutuallyUnbiased_PairSemantics_Values11`, `MutuallyUnbiased_PairSemantics_Values12`, `MutuallyUnbiased_PairSemantics_Values13`, `MutuallyUnbiased_PairSemantics_Values14`, `MutuallyUnbiased_PairSemantics_Values15`, `MutuallyUnbiased_PairSemantics_Values2`, `MutuallyUnbiased_PairSemantics_Values21`, `MutuallyUnbiased_PairSemantics_Values22`, `MutuallyUnbiased_PairSemantics_Values23`, `MutuallyUnbiased_PairSemantics_Values24`, `MutuallyUnbiased_PairSemantics_Values25`, `MutuallyUnbiased_PairSemantics_Values26`, `MutuallyUnbiased_PairSemantics_Values27`, `MutuallyUnbiased_PairSemantics_Values28`, `MutuallyUnbiased_PairSemantics_Values29`, `MutuallyUnbiased_PairSemantics_Values3`, `MutuallyUnbiased_PairSemantics_Values30`, `MutuallyUnbiased_PairSemantics_Values31`, `MutuallyUnbiased_PairSemantics_Values32`, `MutuallyUnbiased_PairSemantics_Values33`, `MutuallyUnbiased_PairSemantics_Values34`, `MutuallyUnbiased_PairSemantics_Values35`, `MutuallyUnbiased_PairSemantics_Values36`, `MutuallyUnbiased_PairSemantics_Values37`, `MutuallyUnbiased_PairSemantics_Values38`, `MutuallyUnbiased_PairSemantics_Values39`, `MutuallyUnbiased_PairSemantics_Values4`, `MutuallyUnbiased_PairSemantics_Values40`, `MutuallyUnbiased_PairSemantics_Values41`, `MutuallyUnbiased_PairSemantics_Values42`, `MutuallyUnbiased_PairSemantics_Values43`, `MutuallyUnbiased_PairSemantics_Values44`, `MutuallyUnbiased_PairSemantics_Values45`, `MutuallyUnbiased_PairSemantics_Values46`, `MutuallyUnbiased_PairSemantics_Values47`, `MutuallyUnbiased_PairSemantics_Values48`, `MutuallyUnbiased_PairSemantics_Values49`, `MutuallyUnbiased_PairSemantics_Values5`, `MutuallyUnbiased_PairSemantics_Values50`, `MutuallyUnbiased_PairSemantics_Values51`, `MutuallyUnbiased_PairSemantics_Values52`, `MutuallyUnbiased_PairSemantics_Values53`, `MutuallyUnbiased_PairSemantics_Values54`, `MutuallyUnbiased_PairSemantics_Values6`, `MutuallyUnbiased_PairSemantics_Values7`, `MutuallyUnbiased_PairSemantics_Values8`, `MutuallyUnbiased_PairSemantics_Values9`, `MutuallyUnbiased_PairTargets_Partition0`, `MutuallyUnbiased_PairTargets_Partition1`, `MutuallyUnbiased_PairTargets_Partition10`, `MutuallyUnbiased_PairTargets_Partition11`, `MutuallyUnbiased_PairTargets_Partition12`, `MutuallyUnbiased_PairTargets_Partition13`, `MutuallyUnbiased_PairTargets_Partition14`, `MutuallyUnbiased_PairTargets_Partition15`, `MutuallyUnbiased_PairTargets_Partition16`, `MutuallyUnbiased_PairTargets_Partition17`, `MutuallyUnbiased_PairTargets_Partition18`, `MutuallyUnbiased_PairTargets_Partition19`, `MutuallyUnbiased_PairTargets_Partition2`, `MutuallyUnbiased_PairTargets_Partition20`, `MutuallyUnbiased_PairTargets_Partition21`, `MutuallyUnbiased_PairTargets_Partition22`, `MutuallyUnbiased_PairTargets_Partition23`, `MutuallyUnbiased_PairTargets_Partition24`, `MutuallyUnbiased_PairTargets_Partition25`, `MutuallyUnbiased_PairTargets_Partition26`, `MutuallyUnbiased_PairTargets_Partition3`, `MutuallyUnbiased_PairTargets_Partition4`, `MutuallyUnbiased_PairTargets_Partition5`, `MutuallyUnbiased_PairTargets_Partition6`, `MutuallyUnbiased_PairTargets_Partition7`, `MutuallyUnbiased_PairTargets_Partition8`, `MutuallyUnbiased_PairTargets_Partition9`.
--
--   **Imports.** It imports the bundle `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e` and `OAI.MUB6.Certificate.PairSemantics.sound3468_e`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E002

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

def value4 : Sparse (Fin 909) := [(1, (1 / 1))]

def value5 : Sparse (Fin 909) := [(0, (-1 / 5))]

def value6 : Sparse (Fin 909) := [(6, (-1 / 4)), (58, (-1 / 4))]

def value7 : Sparse (Fin 909) := [(9, (1 / 1))]

def value8 : Sparse (Fin 909) := [(2, (-1 / 4)), (6, (-1 / 4))]

def value9 : Sparse (Fin 909) := [(5, (1 / 1))]

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

def value33 : Sparse (Fin 909) := [(82, (1 / 1))]

def value34 : Sparse (Fin 909) := [(310, (1 / 1))]

def value35 : Sparse (Fin 909) := [(8, (1 / 1))]

def value36 : Sparse (Fin 909) := [(3, (1 / 1))]

def value37 : Sparse (Fin 909) := [(13, (1 / 1))]

def value38 : Sparse (Fin 909) := [(128, (1 / 1))]

def value39 : Sparse (Fin 909) := [(495, (1 / 1))]

def value40 : Sparse (Fin 909) := [(52, (1 / 1))]

def value41 : Sparse (Fin 909) := [(12, (1 / 1))]

def value42 : Sparse (Fin 909) := [(11, (1 / 1))]

def value43 : Sparse (Fin 909) := [(26, (1 / 1))]

def value44 : Sparse (Fin 909) := [(4, (1 / 1))]

def value45 : Sparse (Fin 909) := [(27, (1 / 1))]

def value46 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (-1 / 6)), (2, (1 / 12))]

def value47 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (1 / 8)), (58, (1 / 16))]

def value48 : Sparse (Fin 909) := [(5, (-1 / 4)), (9, (-1 / 4))]

def value49 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (1 / 16)), (9, (-1 / 4))]

def value50 : Sparse (Fin 909) := [(6, (-3 / 16)), (58, (1 / 16))]

def value51 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 8)), (6, (1 / 16))]

def value52 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 16)), (5, (-1 / 4))]

def value53 : Sparse (Fin 909) := [(2, (-3 / 16)), (6, (1 / 16))]

def value54 : Sparse (Fin 909) := [(2, (1 / 16)), (6, (-3 / 16))]

def value55 : Sparse (Fin 909) := [(6, (1 / 16)), (9, (-1 / 4)), (58, (1 / 16))]

def value56 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (1 / 8)), (2, (1 / 16))]

def value57 : Sparse (Fin 909) := [(1, (-3 / 16)), (2, (1 / 16))]

def value58 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-3 / 16))]

def value59 : Sparse (Fin 909) := [(2, (1 / 16)), (5, (-1 / 4)), (6, (1 / 16))]

def value60 : Sparse (Fin 909) := [(9, (-1 / 2))]

def value61 : Sparse (Fin 909) := [(0, (3 / 80)), (1, (1 / 16))]

def value62 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (-3 / 16))]

def value63 : Sparse (Fin 909) := [(1, (1 / 8)), (2, (1 / 8))]

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

def value64 : Sparse (Fin 909) := [(0, (1 / 10))]

def value65 : Sparse (Fin 909) := [(0, (7 / 60)), (1, (1 / 12))]

def value66 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 8)), (5, (1 / 2)), (6, (-1 / 8)), (9, (5 / 6)), (58, (-1 / 24))]

def value67 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 8)), (5, (1 / 6)), (6, (1 / 8)), (9, (1 / 6)), (58, (-1 / 24))]

def value68 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 6)), (6, (-1 / 12)), (9, (1 / 3))]

def value69 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 4)), (2, (-1 / 3)), (5, (1 / 2)), (6, (-1 / 8))]

def value70 : Sparse (Fin 909) := [(35, (-1 / 3)), (70, (-1 / 3)), (257, (-1 / 3))]

def value71 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 6)), (6, (-1 / 48)), (9, (1 / 4))]

def value72 : Sparse (Fin 909) := [(52, (-1 / 3)), (69, (-1 / 3)), (495, (-1 / 3))]

def value73 : Sparse (Fin 909) := [(69, (-1 / 3)), (70, (-1 / 3)), (71, (-1 / 3))]

def value74 : Sparse (Fin 909) := [(256, (1 / 1))]

def value75 : Sparse (Fin 909) := [(69, (-1 / 3)), (70, (-1 / 3)), (257, (-1 / 3))]

def value76 : Sparse (Fin 909) := [(35, (-1 / 3)), (257, (-1 / 3)), (495, (-1 / 3))]

def value77 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (9, (1 / 6)), (495, (-1 / 3))]

def value78 : Sparse (Fin 909) := [(69, (-1 / 3)), (71, (-2 / 3))]

def value79 : Sparse (Fin 909) := [(35, (-1 / 3)), (60, (-1 / 3)), (257, (-1 / 3))]

def value80 : Sparse (Fin 909) := [(52, (-1 / 3)), (128, (-1 / 3)), (495, (-1 / 3))]

def value81 : Sparse (Fin 909) := [(13, (-1 / 3)), (35, (-1 / 3)), (60, (-1 / 3))]

def value82 : Sparse (Fin 909) := [(2, (-1 / 48)), (5, (1 / 12)), (6, (-1 / 48)), (35, (-1 / 3)), (495, (-1 / 3))]

def value83 : Sparse (Fin 909) := [(13, (-1 / 3)), (52, (-1 / 3)), (128, (-1 / 3))]

def value84 : Sparse (Fin 909) := [(259, (1 / 1))]

def value85 : Sparse (Fin 909) := [(59, (1 / 1))]

def value86 : Sparse (Fin 909) := [(260, (1 / 1))]

def value87 : Sparse (Fin 909) := [(35, (-1 / 3)), (52, (-1 / 3)), (60, (-1 / 3))]

def value88 : Sparse (Fin 909) := [(13, (-1 / 3)), (60, (-1 / 3)), (128, (-1 / 3))]

def value89 : Sparse (Fin 909) := [(262, (1 / 1))]

def value90 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (1 / 6)), (6, (-1 / 24)), (128, (-1 / 3))]

def value91 : Sparse (Fin 909) := [(264, (1 / 1))]

def value92 : Sparse (Fin 909) := [(13, (-1 / 3)), (32, (-1 / 3)), (60, (-1 / 3))]

def value93 : Sparse (Fin 909) := [(13, (-2 / 3)), (32, (-1 / 3))]

def value94 : Sparse (Fin 909) := [(35, (-1 / 3)), (67, (-1 / 3)), (257, (-1 / 3))]

def value95 : Sparse (Fin 909) := [(13, (-1 / 3)), (34, (-1 / 3)), (60, (-1 / 3))]

def value96 : Sparse (Fin 909) := [(266, (1 / 1))]

def value97 : Sparse (Fin 909) := [(61, (1 / 1))]

def value98 : Sparse (Fin 909) := [(62, (1 / 1))]

def value99 : Sparse (Fin 909) := [(267, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value640 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (24, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2))]

def value641 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (3, (1 / 3)), (7, (1 / 6)), (12, (1 / 6)), (23, (-1 / 2))]

def value642 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 6)), (12, (1 / 6)), (23, (-1 / 2)), (25, (-1 / 2)), (54, (-1 / 2))]

def value644 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (228, (-1 / 2)), (726, (-1 / 2))]

def value645 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (5 / 96)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 3)), (26, (1 / 6)), (35, (1 / 6))]

def value646 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-11 / 96)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (7, (1 / 6)), (24, (-1 / 2))]

def value647 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (1 / 96)), (23, (-1 / 2)), (24, (-1 / 2)), (27, (1 / 8)), (55, (-1 / 2))]

def value648 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (13, (1 / 6)), (35, (1 / 6)), (54, (-1 / 2))]

def value649 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (1 / 12)), (6, (1 / 96)), (199, (-1 / 2)), (201, (-1 / 2)), (726, (-1 / 2))]

def value650 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (7, (1 / 6)), (35, (1 / 3)), (82, (1 / 6)), (199, (-1 / 2))]

def value651 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 3)), (12, (1 / 3)), (13, (1 / 2)), (35, (1 / 6)), (54, (-1 / 2))]

def value652 : Sparse (Fin 909) := [(3, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (278, (1 / 6)), (310, (1 / 6)), (495, (1 / 3)), (726, (-1 / 2))]

def value653 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 48)), (2, (1 / 16)), (3, (1 / 3)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 3))]

def value654 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 16)), (2, (1 / 24)), (8, (1 / 6)), (24, (-1 / 2))]

def value655 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (1 / 16)), (2, (1 / 96)), (3, (1 / 6)), (12, (1 / 6))]

def value656 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (13, (1 / 3))]

def value657 : Sparse (Fin 909) := [(3, (1 / 6)), (11, (1 / 6)), (26, (1 / 6)), (52, (1 / 6)), (278, (1 / 6)), (495, (1 / 6))]

def value658 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 48)), (4, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (52, (1 / 6))]

def value659 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (1 / 96)), (2, (1 / 32)), (3, (1 / 6)), (4, (1 / 6))]

def value660 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (4, (1 / 6)), (12, (1 / 6)), (51, (-1 / 2)), (55, (-1 / 2))]

def value661 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 6)), (2, (1 / 48)), (3, (1 / 3)), (12, (1 / 3))]

def value662 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 48)), (2, (1 / 96)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 2)), (35, (1 / 6)), (52, (1 / 6))]

def value663 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (1 / 32)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 2))]

def value664 : Sparse (Fin 909) := [(1, (1 / 96)), (5, (-1 / 12)), (6, (-1 / 96)), (13, (1 / 6)), (35, (1 / 3)), (82, (1 / 3)), (128, (1 / 6)), (278, (1 / 6)), (495, (1 / 6))]

def value665 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (128, (1 / 6)), (201, (-1 / 2))]

def value666 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (4, (1 / 3)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value667 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-7 / 48)), (3, (1 / 3)), (4, (1 / 3)), (12, (1 / 6))]

def value668 : Sparse (Fin 909) := [(0, (1 / 24)), (1, (-5 / 24)), (12, (1 / 6))]

def value669 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 96)), (2, (-1 / 48)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (55, (-1 / 2))]

def value670 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 48)), (2, (1 / 48)), (3, (1 / 2)), (4, (1 / 6)), (12, (1 / 3)), (13, (1 / 6))]

def value671 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (26, (1 / 6)), (35, (1 / 2)), (82, (1 / 6))]

def value672 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 3)), (13, (1 / 3)), (56, (-1 / 2)), (201, (-1 / 2))]

def value673 : Sparse (Fin 909) := [(735, (1 / 1))]

def value674 : Sparse (Fin 909) := [(736, (1 / 1))]

def value675 : Sparse (Fin 909) := [(737, (1 / 1))]

def value676 : Sparse (Fin 909) := [(738, (1 / 1))]

def value677 : Sparse (Fin 909) := [(739, (1 / 1))]

def value678 : Sparse (Fin 909) := [(203, (1 / 1))]

def value679 : Sparse (Fin 909) := [(745, (1 / 1))]

def value680 : Sparse (Fin 909) := [(204, (1 / 1))]

def value681 : Sparse (Fin 909) := [(751, (1 / 1))]

def value682 : Sparse (Fin 909) := [(753, (1 / 1))]

def value683 : Sparse (Fin 909) := [(205, (1 / 1))]

def value684 : Sparse (Fin 909) := [(207, (1 / 1))]

def value685 : Sparse (Fin 909) := [(208, (1 / 1))]

def value686 : Sparse (Fin 909) := [(209, (1 / 1))]

def value687 : Sparse (Fin 909) := [(760, (1 / 1))]

def value688 : Sparse (Fin 909) := [(764, (1 / 1))]

def value689 : Sparse (Fin 909) := [(216, (1 / 1))]

def value690 : Sparse (Fin 909) := [(217, (1 / 1))]

def value691 : Sparse (Fin 909) := [(783, (1 / 1))]

def value692 : Sparse (Fin 909) := [(784, (1 / 1))]

def value693 : Sparse (Fin 909) := [(794, (1 / 1))]

def value694 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 48)), (5, (-1 / 12)), (6, (1 / 32)), (11, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (721, (-1 / 2))]

def value695 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 24)), (52, (1 / 6)), (81, (-1 / 2)), (228, (-1 / 2)), (490, (-1 / 2))]

def value696 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 12)), (3, (1 / 6)), (6, (1 / 96)), (11, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (35, (1 / 2))]

def value697 : Sparse (Fin 909) := [(0, (-1 / 480)), (2, (-1 / 96)), (3, (1 / 3)), (4, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (35, (1 / 6)), (56, (-1 / 2))]

def value698 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (54, (-1 / 2)), (56, (-1 / 2)), (228, (-1 / 2))]

def value699 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (-1 / 12)), (3, (1 / 6)), (26, (1 / 3)), (35, (1 / 6)), (54, (-1 / 2))]

def value700 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (226, (-1 / 2))]

def value701 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 6)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (228, (-1 / 2))]

def value702 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 12)), (2, (-1 / 96)), (3, (1 / 2)), (4, (1 / 6)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value704 : Sparse (Fin 909) := [(1, (-1 / 6)), (3, (1 / 3)), (12, (1 / 3)), (25, (-1 / 2))]

def value705 : Sparse (Fin 909) := [(1, (-11 / 96)), (2, (1 / 96)), (3, (1 / 2)), (4, (1 / 3)), (12, (1 / 6)), (26, (1 / 6))]

def value706 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (25, (-1 / 2)), (26, (1 / 6))]

def value707 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (11, (1 / 6)), (26, (1 / 3)), (35, (1 / 3)), (52, (1 / 6)), (228, (-1 / 2))]

def value708 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 16)), (2, (1 / 32)), (3, (1 / 2)), (4, (1 / 3)), (26, (1 / 3))]

def value709 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-1 / 8)), (2, (1 / 96)), (3, (1 / 6)), (4, (1 / 3))]

def value710 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 96)), (3, (1 / 3)), (26, (1 / 6))]

def value711 : Sparse (Fin 909) := [(0, (3 / 160)), (1, (-13 / 96)), (4, (1 / 6))]

def value712 : Sparse (Fin 909) := [(798, (1 / 1))]

def value713 : Sparse (Fin 909) := [(810, (1 / 1))]

def value714 : Sparse (Fin 909) := [(811, (1 / 1))]

def value715 : Sparse (Fin 909) := [(0, (-1 / 30)), (2, (1 / 2)), (5, (-2 / 3)), (27, (1 / 1)), (68, (2 / 1))]

def value716 : Sparse (Fin 909) := [(0, (1 / 12)), (1, (-3 / 4)), (2, (2 / 3)), (5, (-1 / 2)), (27, (3 / 2))]

def value717 : Sparse (Fin 909) := [(0, (3 / 40)), (1, (-1 / 12)), (5, (-1 / 3)), (6, (1 / 24)), (27, (1 / 2))]

def value718 : Sparse (Fin 909) := [(812, (1 / 1))]

def value719 : Sparse (Fin 909) := [(230, (1 / 1))]

def value720 : Sparse (Fin 909) := [(231, (1 / 1))]

def value721 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 16)), (5, (-1 / 6)), (6, (1 / 32)), (9, (-1 / 12)), (52, (1 / 6)), (310, (1 / 6)), (495, (1 / 6)), (818, (-1 / 2))]

def value722 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 96)), (5, (-1 / 12)), (6, (-1 / 96)), (9, (-1 / 12)), (35, (1 / 6)), (58, (1 / 96)), (278, (1 / 6)), (495, (1 / 3))]

def value723 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (7 / 96)), (2, (11 / 96)), (5, (-1 / 4)), (6, (1 / 16)), (9, (-5 / 24)), (58, (1 / 96))]

def value724 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (6, (1 / 96)), (9, (-5 / 24)), (58, (1 / 96))]

def value725 : Sparse (Fin 909) := [(33, (-1 / 3)), (54, (-1 / 3)), (721, (-1 / 3))]

def value726 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (2 / 9)), (13, (1 / 3)), (59, (-1 / 3))]

def value727 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (13, (1 / 9)), (35, (1 / 9)), (63, (-1 / 3)), (721, (-1 / 3))]

def value728 : Sparse (Fin 909) := [(33, (-1 / 3)), (55, (-1 / 3)), (306, (-1 / 3))]

def value729 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (2 / 9)), (63, (-1 / 3)), (306, (-1 / 3))]

def value730 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (2 / 9)), (26, (2 / 9)), (81, (-1 / 3))]

def value731 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (33, (-1 / 3)), (81, (-1 / 3))]

def value732 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 96)), (5, (-1 / 8)), (6, (1 / 96)), (9, (-1 / 24)), (71, (1 / 6))]

def value733 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (5 / 48)), (2, (5 / 48)), (5, (-1 / 6)), (6, (1 / 48)), (8, (1 / 3)), (71, (1 / 3))]

def value734 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (5 / 48)), (6, (-1 / 32)), (9, (-1 / 24)), (35, (1 / 6)), (70, (1 / 6))]

def value735 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (1 / 16)), (5, (-5 / 24)), (6, (1 / 24)), (8, (1 / 6)), (9, (-1 / 12)), (71, (1 / 3))]

def value736 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 8)), (6, (-1 / 48)), (52, (1 / 6))]

def value737 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 12)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 48)), (8, (1 / 6)), (52, (1 / 6))]

def value738 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 6)), (35, (1 / 6))]

def value739 : Sparse (Fin 909) := [(1, (-5 / 96)), (2, (-1 / 16)), (5, (-1 / 8)), (6, (1 / 32)), (7, (1 / 6)), (35, (1 / 6))]

def value740 : Sparse (Fin 909) := [(1, (1 / 48)), (5, (-1 / 24)), (6, (-1 / 16)), (11, (1 / 6)), (35, (1 / 6))]

def value741 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (11 / 96)), (3, (1 / 6)), (5, (-1 / 6)), (6, (1 / 32)), (35, (1 / 6)), (52, (1 / 3))]

def value742 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (35, (1 / 6)), (52, (1 / 3))]

def value743 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (52, (1 / 6)), (228, (-1 / 2))]

def value744 : Sparse (Fin 909) := [(2, (-1 / 12)), (5, (-1 / 12)), (11, (1 / 6)), (26, (1 / 6)), (35, (1 / 3))]

def value745 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-3 / 32)), (6, (-3 / 32)), (11, (1 / 3)), (35, (1 / 6)), (58, (1 / 96)), (278, (1 / 6))]

def value746 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (-5 / 96)), (5, (-1 / 12)), (6, (-1 / 48)), (9, (-1 / 24)), (58, (1 / 96))]

def value747 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (6, (-5 / 96)), (9, (-1 / 24)), (58, (1 / 96))]

def value748 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (1 / 24)), (5, (-1 / 8)), (6, (1 / 32))]

def value749 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (-1 / 16)), (5, (1 / 24)), (6, (-1 / 96))]

def value750 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (8, (2 / 9)), (69, (1 / 9)), (71, (1 / 3))]

def value751 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (7, (2 / 9)), (69, (2 / 9)), (70, (1 / 9)), (71, (1 / 9))]

def value752 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 9)), (256, (-1 / 3))]

def value753 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (35, (1 / 9)), (256, (-1 / 3)), (277, (-1 / 3))]

def value754 : Sparse (Fin 909) := [(7, (-1 / 9)), (69, (2 / 9)), (70, (2 / 9))]

def value755 : Sparse (Fin 909) := [(8, (-1 / 9)), (71, (4 / 9))]

def value756 : Sparse (Fin 909) := [(33, (-1 / 3)), (81, (-1 / 3)), (490, (-1 / 3))]

def value757 : Sparse (Fin 909) := [(33, (-1 / 3)), (306, (-1 / 3)), (721, (-1 / 3))]

def value758 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (35, (1 / 9)), (52, (1 / 9)), (123, (-1 / 3)), (721, (-1 / 3))]

def value759 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (34, (1 / 9)), (273, (-1 / 3)), (490, (-1 / 3))]

def value760 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (7, (2 / 9)), (35, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value761 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 144)), (2, (1 / 24)), (5, (-1 / 18)), (6, (1 / 144)), (8, (2 / 9)), (71, (2 / 9))]

def value762 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (5, (-1 / 12)), (8, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value763 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value764 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value765 : Sparse (Fin 909) := [(3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9)), (13, (2 / 9)), (35, (2 / 9)), (60, (1 / 9))]

def value766 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (7 / 144)), (2, (1 / 18)), (5, (-1 / 18)), (8, (1 / 9)), (52, (1 / 9))]

def value767 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value768 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (35, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value769 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (1 / 36)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value770 : Sparse (Fin 909) := [(51, (-1 / 3)), (259, (-1 / 3)), (308, (-1 / 3))]

def value771 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 144)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 18)), (7, (2 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value772 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (51, (-1 / 3)), (59, (-1 / 3))]

def value773 : Sparse (Fin 909) := [(3, (1 / 9)), (10, (-1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (59, (-1 / 3))]

def value774 : Sparse (Fin 909) := [(3, (-1 / 9)), (7, (1 / 9)), (35, (2 / 9)), (52, (1 / 9))]

def value775 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (-1 / 9)), (35, (1 / 9))]

def value776 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (69, (1 / 9)), (124, (-1 / 3)), (259, (-1 / 3))]

def value777 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (2 / 9)), (34, (1 / 9)), (35, (1 / 9)), (60, (1 / 9)), (273, (-1 / 3))]

def value778 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (1 / 9)), (52, (1 / 9)), (260, (-1 / 3)), (309, (-1 / 3))]

def value779 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (2 / 9)), (52, (1 / 9)), (60, (1 / 9))]

def value780 : Sparse (Fin 909) := [(1, (1 / 48)), (5, (-1 / 36)), (6, (1 / 144)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (60, (1 / 9)), (128, (1 / 9))]

def value781 : Sparse (Fin 909) := [(13, (-1 / 9)), (35, (1 / 9)), (60, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value782 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (-1 / 9)), (52, (1 / 9)), (60, (1 / 9))]

def value783 : Sparse (Fin 909) := [(7, (1 / 9)), (35, (1 / 9)), (70, (1 / 9)), (125, (-1 / 3)), (260, (-1 / 3))]

def value784 : Sparse (Fin 909) := [(51, (-1 / 3)), (262, (-1 / 3)), (309, (-1 / 3))]

def value785 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (52, (1 / 9)), (262, (-1 / 3)), (308, (-1 / 3))]

def value786 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 24)), (5, (-1 / 12)), (7, (1 / 9)), (8, (2 / 9))]

def value787 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 36)), (5, (-1 / 18)), (8, (-1 / 9))]

def value788 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (71, (1 / 9)), (126, (-1 / 3)), (262, (-1 / 3))]

def value789 : Sparse (Fin 909) := [(23, (-1 / 3)), (124, (-1 / 3)), (196, (-1 / 3))]

def value790 : Sparse (Fin 909) := [(24, (-1 / 3)), (126, (-1 / 3)), (197, (-1 / 3))]

def value791 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (125, (-1 / 3)), (126, (-1 / 3))]

def value792 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (5, (-1 / 18)), (7, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 9)), (260, (-1 / 3))]

def value793 : Sparse (Fin 909) := [(23, (-1 / 3)), (125, (-2 / 3))]

def value794 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (124, (-1 / 3)), (197, (-1 / 3))]

def value795 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (-1 / 9)), (35, (1 / 9)), (69, (1 / 9)), (70, (1 / 9))]

def value796 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (-1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (35, (1 / 9))]

def value797 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 24)), (2, (1 / 18)), (3, (1 / 9)), (5, (-1 / 36)), (13, (1 / 9)), (52, (1 / 9))]

def value798 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (52, (2 / 9)), (60, (1 / 9)), (128, (1 / 9))]

def value799 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value800 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (-1 / 144)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value801 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (5 / 144)), (3, (2 / 9)), (4, (1 / 9)), (13, (1 / 9))]

def value802 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (12, (2 / 9)), (13, (2 / 9))]

def value803 : Sparse (Fin 909) := [(1, (-1 / 18)), (2, (-1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value804 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (51, (-1 / 3)), (54, (-1 / 3))]

def value805 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-5 / 144)), (2, (1 / 36)), (3, (2 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value806 : Sparse (Fin 909) := [(3, (1 / 9)), (12, (-1 / 9)), (13, (1 / 3))]

def value807 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (-1 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value808 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (7, (1 / 9)), (23, (-1 / 3)), (54, (-1 / 3))]

def value809 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (13, (2 / 9)), (52, (1 / 9)), (62, (-1 / 3))]

def value810 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (13, (4 / 9)), (32, (1 / 9))]

def value811 : Sparse (Fin 909) := [(12, (1 / 9)), (13, (1 / 9)), (32, (1 / 9))]

def value812 : Sparse (Fin 909) := [(3, (1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (54, (-1 / 3)), (62, (-1 / 3))]

def value813 : Sparse (Fin 909) := [(2, (1 / 144)), (5, (-1 / 36)), (6, (1 / 144)), (52, (1 / 9)), (128, (1 / 9)), (201, (-1 / 3)), (267, (-1 / 3))]

def value814 : Sparse (Fin 909) := [(13, (1 / 9)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 3)), (267, (-1 / 3))]

def value815 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (51, (-1 / 3)), (56, (-1 / 3))]

def value816 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (-1 / 9)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value817 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (2 / 9)), (52, (-1 / 9)), (60, (1 / 9))]

def value818 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (60, (1 / 9))]

def value819 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (5 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (13, (1 / 9)), (35, (1 / 9))]

def value820 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (24, (-1 / 3)), (56, (-1 / 3))]

def value821 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (81, (-1 / 3)), (307, (-1 / 3))]

def value822 : Sparse (Fin 909) := [(25, (-1 / 3)), (31, (-1 / 3)), (123, (-1 / 3))]

def value823 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (33, (-1 / 3)), (64, (-1 / 3))]

def value824 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (33, (-1 / 3)), (123, (-1 / 3))]

def value825 : Sparse (Fin 909) := [(23, (-1 / 3)), (25, (-1 / 3)), (63, (-1 / 3))]

def value826 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (5, (-1 / 36)), (7, (2 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value827 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (1 / 3)), (4, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value828 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (24, (-1 / 3)), (55, (-1 / 3))]

def value829 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (64, (-1 / 3))]

def value830 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (7, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (271, (-1 / 3))]

def value831 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (23, (-1 / 3)), (55, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value832 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (-1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value833 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value834 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (35, (2 / 9)), (52, (1 / 9)), (67, (1 / 9))]

def value835 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (1 / 36)), (3, (1 / 9)), (4, (1 / 9))]

def value836 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value837 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (1 / 48)), (3, (2 / 9)), (12, (1 / 9))]

def value838 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9))]

def value839 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (1 / 3)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value840 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (3, (2 / 9)), (12, (1 / 9)), (26, (1 / 9))]

def value841 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (1 / 9)), (26, (1 / 9)), (55, (-1 / 3)), (65, (-1 / 3))]

def value842 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 24)), (3, (2 / 9)), (4, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3))]

def value843 : Sparse (Fin 909) := [(3, (-1 / 9)), (12, (1 / 9)), (13, (2 / 9)), (34, (1 / 9))]

def value844 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (12, (1 / 9)), (25, (-1 / 3)), (33, (-1 / 3))]

def value845 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 144)), (3, (2 / 9)), (4, (2 / 9)), (12, (1 / 9)), (26, (1 / 9))]

def value846 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (4, (-1 / 9)), (26, (1 / 9))]

def value847 : Sparse (Fin 909) := [(3, (-1 / 9)), (4, (1 / 9)), (26, (2 / 9)), (34, (1 / 9))]

def value848 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (228, (-1 / 3)), (275, (-1 / 3))]

def value849 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value850 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 36)), (2, (1 / 48)), (3, (1 / 3)), (26, (2 / 9)), (34, (1 / 9))]

def value851 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (2 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value852 : Sparse (Fin 909) := [(3, (2 / 9)), (12, (1 / 9)), (13, (2 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value853 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (2 / 9)), (4, (1 / 9)), (12, (2 / 9)), (13, (1 / 9))]

def value854 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (12, (-1 / 9)), (13, (1 / 9))]

def value855 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (1 / 32)), (5, (-1 / 12)), (6, (1 / 96)), (8, (1 / 6)), (71, (1 / 6)), (236, (-1 / 2))]

def value856 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (8, (1 / 6)), (30, (-1 / 2)), (236, (-1 / 1))]

def value857 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (27, (1 / 8)), (68, (1 / 4)), (126, (-1 / 2)), (236, (-1 / 2))]

def value858 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (5, (-1 / 24)), (27, (1 / 8)), (126, (-1 / 2)), (236, (-1 / 2))]

def value859 : Sparse (Fin 909) := [(1, (1 / 32)), (5, (-1 / 24)), (6, (1 / 96)), (68, (1 / 4)), (197, (-1 / 2)), (236, (-1 / 2))]

def value860 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 32)), (5, (-1 / 12)), (6, (1 / 48)), (71, (1 / 6)), (197, (-1 / 2))]

def value861 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (9, (-1 / 12)), (71, (1 / 6)), (796, (-1 / 2))]

def value862 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (-1 / 24)), (5, (-1 / 12)), (6, (1 / 48))]

def value863 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6))]

def value864 : Sparse (Fin 909) := [(1, (-1 / 16)), (5, (-1 / 24)), (6, (1 / 48)), (26, (1 / 6)), (35, (1 / 6))]

def value865 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 16)), (5, (-1 / 8)), (6, (-5 / 96)), (35, (1 / 6)), (82, (1 / 6))]

def value866 : Sparse (Fin 909) := [(0, (-1 / 80)), (1, (1 / 12)), (2, (5 / 48)), (5, (-1 / 12)), (8, (1 / 3))]

def value867 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 48)), (52, (1 / 6)), (237, (-1 / 2))]

def value868 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (3, (1 / 6))]

def value869 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (-5 / 96)), (3, (1 / 6)), (26, (1 / 6))]

def value870 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (1 / 48)), (2, (5 / 48)), (3, (1 / 3)), (5, (-1 / 24)), (52, (1 / 6))]

def value871 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 6)), (31, (-1 / 2)), (237, (-1 / 2)), (238, (-1 / 2))]

def value872 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (1 / 48)), (3, (1 / 3)), (4, (1 / 6)), (26, (1 / 6))]

def value873 : Sparse (Fin 909) := [(0, (-1 / 480)), (2, (1 / 32)), (5, (-1 / 24)), (27, (1 / 4)), (55, (-1 / 2)), (237, (-1 / 2))]

def value874 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 12)), (27, (1 / 8)), (68, (1 / 8)), (238, (-1 / 2)), (493, (-1 / 2))]

def value875 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (26, (1 / 6)), (35, (1 / 6)), (238, (-1 / 2))]

def value876 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-3 / 32)), (2, (-3 / 32)), (3, (1 / 6)), (6, (1 / 96)), (26, (1 / 3)), (35, (1 / 6))]

def value877 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (5 / 96)), (5, (1 / 12)), (6, (1 / 48)), (9, (-1 / 24)), (35, (1 / 6)), (727, (-1 / 2))]

def value878 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 96)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 48)), (9, (-1 / 24)), (27, (1 / 8)), (68, (1 / 8))]

def value879 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 32)), (6, (1 / 48)), (9, (-1 / 24)), (68, (1 / 8))]

def value880 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-7 / 96)), (5, (1 / 24)), (6, (-5 / 96)), (9, (-1 / 24)), (58, (1 / 96))]

def value881 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-1 / 12)), (5, (-1 / 24)), (6, (1 / 96))]

def value882 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (1 / 48)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 96))]

def value883 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 24)), (2, (1 / 48)), (5, (-1 / 24)), (6, (-1 / 96))]

def value884 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-1 / 8)), (2, (-1 / 48))]

def value885 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 24)), (2, (1 / 48)), (5, (-1 / 12)), (6, (1 / 96)), (27, (1 / 8))]

def value886 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 36)), (52, (1 / 9)), (256, (-1 / 3)), (818, (-1 / 3))]

def value887 : Sparse (Fin 909) := [(3, (1 / 9)), (35, (1 / 9)), (52, (1 / 9)), (256, (-1 / 3)), (726, (-1 / 3))]

def value888 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 144)), (5, (-1 / 12)), (6, (1 / 72)), (7, (1 / 9)), (9, (-1 / 18)), (69, (1 / 9)), (70, (1 / 9))]

def value889 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 12)), (6, (1 / 72)), (8, (1 / 9)), (9, (-1 / 18)), (71, (2 / 9))]

def value890 : Sparse (Fin 909) := [(1, (-1 / 144)), (6, (1 / 144)), (9, (-1 / 18)), (69, (1 / 9)), (71, (1 / 9))]

def value891 : Sparse (Fin 909) := [(855, (1 / 1))]

def value892 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (-1 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (52, (1 / 9))]

def value893 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 72)), (35, (1 / 9)), (52, (2 / 9))]

def value894 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9)), (81, (-1 / 3))]

def value895 : Sparse (Fin 909) := [(55, (-1 / 3)), (306, (-1 / 3)), (728, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value896 : Sparse (Fin 909) := [(3, (1 / 9)), (4, (1 / 9)), (26, (1 / 9)), (81, (-1 / 3)), (228, (-1 / 3))]

def value897 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (35, (1 / 9)), (52, (-1 / 9))]

def value898 : Sparse (Fin 909) := [(1, (-1 / 144)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value899 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 18)), (6, (1 / 144)), (26, (2 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value900 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (35, (1 / 9)), (238, (-1 / 3)), (307, (-1 / 3))]

def value901 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (307, (-1 / 3)), (727, (-1 / 3))]

def value902 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (-1 / 9)), (35, (2 / 9)), (67, (1 / 9))]

def value903 : Sparse (Fin 909) := [(3, (1 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (-1 / 9)), (67, (1 / 9))]

def value904 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (7 / 144)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (9, (-1 / 36)), (69, (1 / 9))]

def value905 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 24)), (5, (-1 / 36)), (6, (1 / 48)), (7, (1 / 9)), (9, (-1 / 36)), (35, (1 / 9)), (70, (1 / 9))]

def value906 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 72)), (2, (1 / 18)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9))]

def value907 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (7, (1 / 9)), (35, (1 / 9))]

def value908 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (-5 / 144)), (5, (-1 / 36)), (6, (-1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (82, (1 / 9))]

def value909 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 48)), (5, (-1 / 18)), (6, (-1 / 144))]

def value910 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9))]

def value911 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (7, (1 / 9)), (11, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value912 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 36)), (5, (1 / 36)), (10, (-1 / 3)), (27, (1 / 12))]

def value913 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (9, (-1 / 36)), (27, (1 / 12)), (68, (1 / 12)), (308, (-1 / 3))]

def value914 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (8, (1 / 9))]

def value915 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (-1 / 72)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9))]

def value916 : Sparse (Fin 909) := [(10, (-1 / 3)), (55, (-1 / 3)), (727, (-1 / 3))]

def value917 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 144)), (3, (2 / 9)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3))]

def value918 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 144)), (5, (-1 / 18)), (6, (1 / 72)), (9, (-1 / 36)), (68, (1 / 12)), (309, (-1 / 3))]

def value919 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 72)), (5, (-1 / 36)), (6, (-1 / 144)), (35, (1 / 9))]

def value920 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 24)), (6, (1 / 144)), (11, (1 / 9)), (26, (1 / 9)), (35, (-1 / 9))]

def value921 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (1 / 24)), (3, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value922 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (52, (1 / 9))]

def value923 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (6, (1 / 144)), (8, (1 / 9)), (71, (2 / 9)), (236, (-1 / 3))]

def value924 : Sparse (Fin 909) := [(239, (1 / 1))]

def value925 : Sparse (Fin 909) := [(870, (1 / 1))]

def value926 : Sparse (Fin 909) := [(57, (1 / 1))]

def value927 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (35, (1 / 9)), (52, (1 / 9)), (81, (-1 / 3)), (306, (-1 / 3))]

def value928 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (13, (2 / 9)), (33, (-1 / 3)), (63, (-1 / 3))]

def value929 : Sparse (Fin 909) := [(13, (1 / 9)), (52, (1 / 9)), (59, (-1 / 3)), (128, (1 / 9)), (721, (-1 / 3))]

def value930 : Sparse (Fin 909) := [(30, (-1 / 3)), (236, (-2 / 3))]

def value931 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 36)), (2, (1 / 72)), (8, (1 / 9)), (126, (-1 / 3)), (236, (-1 / 3))]

def value932 : Sparse (Fin 909) := [(56, (-1 / 3)), (262, (-1 / 3)), (796, (-1 / 3))]

def value933 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (52, (1 / 9))]

def value934 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 72)), (13, (1 / 9)), (52, (2 / 9)), (128, (1 / 9))]

def value935 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 48)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (13, (2 / 9)), (35, (1 / 9)), (52, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value936 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-5 / 144)), (2, (1 / 24)), (3, (1 / 9))]

def value937 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (3, (1 / 9)), (13, (2 / 9))]

def value938 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (-1 / 144)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 3)), (35, (1 / 9))]

def value939 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 144)), (2, (1 / 36)), (3, (2 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value940 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (1 / 24)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value941 : Sparse (Fin 909) := [(31, (-1 / 3)), (123, (-1 / 3)), (237, (-1 / 3))]

def value942 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (26, (1 / 9))]

def value943 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3))]

def value944 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (33, (-1 / 3)), (55, (-1 / 3))]

def value945 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (-1 / 9)), (26, (2 / 9))]

def value946 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (1 / 144)), (3, (-1 / 9)), (4, (1 / 9)), (26, (1 / 9))]

def value947 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (123, (-1 / 3))]

def value948 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (3, (1 / 9)), (64, (-1 / 3)), (238, (-1 / 3))]

def value949 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 18)), (2, (-1 / 144)), (3, (2 / 9)), (26, (2 / 9)), (34, (1 / 9))]

def value950 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 72)), (2, (1 / 144)), (3, (2 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9))]

def value951 : Sparse (Fin 909) := [(3, (-1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (1 / 9)), (35, (1 / 9))]

def value952 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (26, (-1 / 9)), (34, (1 / 9))]

def value953 : Sparse (Fin 909) := [(3, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (55, (-1 / 3)), (64, (-1 / 3))]

def value954 : Sparse (Fin 909) := [(11, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (228, (-1 / 3)), (490, (-1 / 3))]

def value955 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (1 / 144)), (27, (1 / 6)), (68, (1 / 12)), (124, (-1 / 3))]

def value956 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 18)), (68, (1 / 12)), (125, (-1 / 3))]

def value957 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 48)), (5, (1 / 9)), (6, (1 / 72)), (9, (-1 / 36)), (492, (-1 / 3))]

def value958 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (1 / 48)), (5, (-1 / 36)), (27, (1 / 12)), (68, (1 / 12)), (126, (-1 / 3))]

def value959 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 18)), (2, (5 / 144)), (3, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9))]

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

def value960 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (-1 / 24)), (3, (1 / 9)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9))]

def value961 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (13, (1 / 9)), (82, (1 / 9)), (128, (1 / 9))]

def value962 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 48)), (2, (1 / 144)), (5, (-1 / 18)), (6, (-1 / 144)), (52, (1 / 9))]

def value963 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 72)), (5, (-1 / 36)), (6, (1 / 144))]

def value964 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 48)), (2, (1 / 24)), (5, (-1 / 36)), (8, (1 / 9))]

def value965 : Sparse (Fin 909) := [(3, (2 / 9)), (4, (1 / 9)), (11, (1 / 9)), (13, (1 / 9)), (26, (2 / 9)), (35, (2 / 9))]

def value966 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-1 / 18)), (2, (1 / 48)), (3, (1 / 9))]

def value967 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 9)), (12, (1 / 9)), (13, (1 / 9))]

def value968 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (52, (1 / 9))]

def value969 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-1 / 24)), (2, (1 / 144))]

def value970 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 48)), (2, (1 / 36))]

def value971 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (1 / 3)), (4, (1 / 9)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 9))]

def value972 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 48)), (2, (1 / 36)), (5, (-1 / 18)), (8, (1 / 9))]

def value973 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 72)), (2, (1 / 36)), (5, (-1 / 36)), (27, (1 / 12)), (51, (-1 / 3))]

def value974 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (1 / 48)), (3, (1 / 9))]

def value975 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (3, (2 / 9)), (12, (2 / 9)), (13, (1 / 9)), (55, (-1 / 3))]

def value976 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 72)), (3, (2 / 9)), (7, (2 / 9)), (24, (-1 / 3))]

def value977 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 36)), (5, (-1 / 36)), (6, (1 / 144)), (13, (1 / 9)), (52, (1 / 9))]

def value978 : Sparse (Fin 909) := [(0, (-1 / 720)), (2, (7 / 144)), (13, (1 / 9))]

def value979 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 144)), (3, (1 / 9)), (13, (-1 / 9)), (35, (1 / 9))]

def value980 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (-1 / 48)), (3, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (56, (-1 / 3))]

def value981 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (52, (1 / 9)), (128, (1 / 9))]

def value982 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (7 / 144)), (2, (7 / 144)), (3, (1 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (13, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value983 : Sparse (Fin 909) := [(31, (-1 / 3)), (51, (-1 / 3)), (238, (-1 / 3))]

def value984 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 24)), (2, (5 / 144)), (3, (2 / 9)), (52, (1 / 9)), (237, (-1 / 3))]

def value985 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 24)), (5, (-1 / 18)), (6, (1 / 72)), (52, (-1 / 9))]

def value986 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 144)), (5, (-1 / 9)), (6, (1 / 48)), (8, (1 / 9)), (52, (1 / 9))]

def value987 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 18)), (2, (1 / 36)), (8, (2 / 9)), (30, (-1 / 3))]

def value988 : Sparse (Fin 909) := [(26, (1 / 9)), (35, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3)), (273, (-1 / 3))]

def value989 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-5 / 144)), (63, (-1 / 3)), (123, (-1 / 3))]

def value990 : Sparse (Fin 909) := [(3, (2 / 9)), (13, (1 / 9)), (26, (1 / 9)), (34, (2 / 9)), (64, (-1 / 3))]

def value991 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (-1 / 72)), (5, (-1 / 36)), (124, (-1 / 3)), (236, (-1 / 3))]

def value992 : Sparse (Fin 909) := [(1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 48)), (71, (1 / 9)), (259, (-1 / 3))]

def value993 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (1 / 36)), (5, (-1 / 36)), (126, (-2 / 3))]

def value994 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (-1 / 144)), (5, (1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 9))]

def value995 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (5 / 144)), (2, (5 / 144)), (8, (1 / 9)), (51, (-1 / 3))]

def value996 : Sparse (Fin 909) := [(1, (5 / 144)), (2, (5 / 144)), (5, (-1 / 12)), (8, (1 / 9)), (52, (1 / 9)), (59, (-1 / 3))]

def value997 : Sparse (Fin 909) := [(1, (1 / 72)), (2, (1 / 72)), (3, (1 / 9)), (13, (1 / 9)), (59, (-1 / 3)), (201, (-1 / 3))]

def value998 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 48)), (5, (-1 / 18)), (7, (1 / 9)), (8, (-1 / 9))]

def value999 : Sparse (Fin 909) := [(1, (1 / 144)), (2, (1 / 144)), (5, (-1 / 36)), (8, (1 / 9)), (69, (1 / 9)), (71, (1 / 3)), (256, (-1 / 3))]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value1406 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (1 / 32)), (2, (1 / 96)), (3, (-2 / 3)), (4, (-1 / 6)), (12, (-1 / 3)), (13, (-2 / 3)), (26, (-1 / 6)), (35, (-1 / 3)), (51, (1 / 1)), (54, (1 / 1)), (55, (1 / 2)), (56, (1 / 1)), (59, (1 / 2)), (61, (1 / 1)), (259, (1 / 2)), (262, (1 / 2)), (266, (1 / 2)), (268, (1 / 2))]

def value1407 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 48)), (2, (-1 / 16)), (3, (-2 / 3)), (5, (1 / 12)), (6, (-1 / 48)), (12, (-1 / 6)), (13, (-8 / 3)), (32, (-2 / 3)), (35, (-2 / 3)), (52, (-2 / 3)), (60, (-2 / 3)), (62, (1 / 1)), (128, (-1 / 6))]

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

def value3192 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (31 / 288)), (2, (17 / 96)), (3, (5 / 6)), (5, (-1 / 4)), (6, (5 / 144)), (7, (2 / 9)), (8, (1 / 9)), (10, (-1 / 6)), (12, (1 / 6)), (13, (5 / 9)), (33, (-1 / 6)), (35, (5 / 9)), (52, (2 / 3)), (59, (-1 / 6)), (75, (1 / 2)), (82, (1 / 9)), (128, (1 / 9)), (201, (-1 / 2)), (306, (-1 / 6)), (313, (1 / 2)), (721, (-1 / 6)), (760, (1 / 2))]

def value3193 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-7 / 36)), (2, (1 / 32)), (3, (5 / 9)), (4, (2 / 3)), (12, (1 / 9)), (15, (1 / 2)), (20, (1 / 1)), (24, (-1 / 2))]

def value3194 : Sparse (Fin 909) := [(0, (-1 / 360)), (2, (3 / 32)), (3, (5 / 6)), (4, (5 / 18)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 2)), (8, (2 / 9)), (11, (1 / 9)), (26, (4 / 9)), (33, (-1 / 6)), (35, (11 / 18)), (52, (2 / 9)), (67, (1 / 18)), (81, (-1 / 2)), (85, (1 / 1)), (228, (-5 / 6)), (428, (1 / 2)), (517, (1 / 2))]

def value3195 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 144)), (2, (31 / 288)), (3, (17 / 18)), (4, (5 / 18)), (5, (-1 / 6)), (6, (1 / 96)), (7, (4 / 9)), (8, (2 / 9)), (11, (1 / 9)), (26, (1 / 2)), (35, (1 / 2)), (52, (2 / 9)), (81, (-5 / 6)), (85, (1 / 1)), (228, (-5 / 6)), (709, (1 / 2))]

def value3196 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-23 / 144)), (2, (1 / 12)), (3, (5 / 6)), (4, (4 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (8, (1 / 9)), (24, (-1 / 3)), (26, (5 / 18)), (31, (-1 / 3)), (37, (1 / 2)), (56, (-1 / 6)), (99, (1 / 1)), (107, (1 / 1))]

def value3197 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-5 / 36)), (2, (19 / 288)), (3, (11 / 9)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (26, (13 / 18)), (37, (1 / 2)), (56, (-1 / 6))]

def value3198 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (-5 / 32)), (2, (5 / 144)), (3, (1 / 3)), (19, (1 / 2)), (24, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 6))]

def value3199 : Sparse (Fin 909) := [(0, (3 / 160)), (1, (-37 / 144)), (2, (13 / 288)), (3, (1 / 6)), (4, (7 / 18)), (20, (1 / 2)), (24, (-1 / 6)), (27, (1 / 24)), (30, (-1 / 6)), (31, (-1 / 6))]

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

def value320 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (7 / 96)), (5, (-1 / 6)), (6, (1 / 24)), (13, (1 / 6)), (52, (1 / 3)), (128, (1 / 6))]

def value321 : Sparse (Fin 909) := [(51, (-1 / 2)), (59, (-1 / 2)), (259, (-1 / 2)), (262, (-1 / 2))]

def value322 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (5, (-1 / 6)), (7, (1 / 3)), (8, (1 / 3)), (35, (1 / 6)), (59, (-1 / 2))]

def value323 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (13, (1 / 3)), (52, (1 / 3)), (60, (1 / 6)), (128, (1 / 3)), (260, (-1 / 2)), (495, (1 / 6))]

def value324 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (60, (1 / 3)), (128, (1 / 6))]

def value325 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (13, (1 / 6)), (35, (1 / 6)), (63, (-1 / 2)), (196, (-1 / 2)), (264, (-1 / 2))]

def value326 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 3)), (35, (1 / 2)), (67, (1 / 6)), (69, (1 / 6)), (70, (1 / 3)), (257, (1 / 6))]

def value327 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (13, (1 / 6)), (52, (1 / 6)), (64, (-1 / 2)), (125, (-1 / 2)), (260, (-1 / 2))]

def value328 : Sparse (Fin 909) := [(124, (-1 / 2)), (196, (-1 / 2)), (197, (-1 / 2)), (266, (-1 / 2))]

def value329 : Sparse (Fin 909) := [(263, (1 / 1))]

def value330 : Sparse (Fin 909) := [(125, (-1 / 1)), (264, (-1 / 1))]

def value331 : Sparse (Fin 909) := [(54, (-1 / 2)), (62, (-1 / 2)), (260, (-1 / 2)), (264, (-1 / 2))]

def value332 : Sparse (Fin 909) := [(125, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2)), (268, (-1 / 2))]

def value333 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (13, (1 / 3)), (32, (1 / 6)), (35, (1 / 3)), (60, (1 / 3)), (257, (1 / 6)), (264, (-1 / 2))]

def value334 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 96)), (13, (1 / 6)), (32, (1 / 6)), (35, (1 / 6)), (60, (1 / 6))]

def value335 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 96)), (26, (1 / 6)), (67, (1 / 6)), (257, (1 / 6)), (495, (1 / 6))]

def value336 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (34, (1 / 6)), (52, (1 / 6)), (60, (1 / 6)), (128, (1 / 6))]

def value337 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (26, (1 / 6)), (35, (1 / 6)), (54, (-1 / 2)), (259, (-1 / 2)), (266, (-1 / 2))]

def value338 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (12, (1 / 6)), (13, (1 / 2)), (59, (-1 / 2)), (61, (-1 / 2))]

def value339 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (13, (1 / 2)), (32, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (60, (1 / 6)), (62, (-1 / 2))]

def value340 : Sparse (Fin 909) := [(12, (1 / 6)), (13, (1 / 1)), (32, (1 / 3)), (60, (1 / 3)), (128, (1 / 6))]

def value341 : Sparse (Fin 909) := [(1, (1 / 16)), (2, (-1 / 48)), (13, (1 / 1)), (32, (1 / 3))]

def value342 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 32)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 3)), (67, (1 / 3)), (257, (1 / 6)), (266, (-1 / 2))]

def value343 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (13, (1 / 3)), (26, (1 / 6)), (34, (1 / 3)), (60, (1 / 6)), (61, (-1 / 2))]

def value344 : Sparse (Fin 909) := [(54, (-1 / 2)), (65, (-1 / 2)), (264, (-1 / 2)), (266, (-1 / 2))]

def value345 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (54, (-1 / 2)), (62, (-1 / 2))]

def value346 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (12, (1 / 3)), (13, (1 / 1)), (32, (1 / 6))]

def value347 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (2 / 3)), (32, (1 / 6)), (34, (1 / 6)), (60, (1 / 6)), (61, (-1 / 2))]

def value348 : Sparse (Fin 909) := [(3, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (60, (1 / 6)), (67, (1 / 6)), (257, (1 / 6)), (268, (-1 / 2))]

def value349 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (-1 / 96)), (3, (1 / 3)), (13, (1 / 3)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (60, (1 / 6))]

def value350 : Sparse (Fin 909) := [(55, (-1 / 2)), (61, (-1 / 2)), (266, (-1 / 2)), (268, (-1 / 2))]

def value351 : Sparse (Fin 909) := [(51, (-1 / 2)), (54, (-1 / 2)), (56, (-1 / 2)), (61, (-1 / 2))]

def value352 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 3)), (26, (1 / 6)), (35, (2 / 3)), (67, (1 / 3)), (70, (1 / 6)), (257, (1 / 6))]

def value353 : Sparse (Fin 909) := [(55, (-1 / 2)), (64, (-1 / 2)), (125, (-1 / 2)), (266, (-1 / 2))]

def value354 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (-1 / 16)), (13, (1 / 2)), (35, (1 / 6)), (63, (-1 / 2))]

def value355 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (1 / 3)), (7, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 3)), (67, (1 / 6))]

def value356 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 6)), (33, (-1 / 2)), (55, (-1 / 2)), (64, (-1 / 2))]

def value357 : Sparse (Fin 909) := [(23, (-1 / 2)), (55, (-1 / 2)), (63, (-1 / 2)), (65, (-1 / 2))]

def value358 : Sparse (Fin 909) := [(25, (-1 / 2)), (33, (-1 / 2)), (63, (-1 / 2)), (64, (-1 / 2))]

def value359 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 3)), (35, (1 / 2)), (67, (1 / 3)), (271, (-1 / 2)), (276, (1 / 6))]

def value360 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (7, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 6)), (64, (-1 / 2)), (67, (1 / 6))]

def value361 : Sparse (Fin 909) := [(24, (-1 / 2)), (55, (-1 / 1)), (66, (-1 / 2))]

def value362 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 2)), (67, (1 / 3))]

def value363 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 96)), (3, (1 / 3)), (13, (1 / 3)), (34, (1 / 6)), (52, (1 / 6)), (64, (-1 / 2))]

def value364 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-7 / 48)), (13, (1 / 3))]

def value365 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-1 / 48)), (3, (1 / 6)), (34, (1 / 6)), (35, (1 / 6)), (67, (1 / 6))]

def value366 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 96)), (2, (1 / 24)), (13, (1 / 6)), (26, (1 / 6)), (34, (1 / 6))]

def value367 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (54, (-1 / 2)), (65, (-1 / 2))]

def value368 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 32)), (2, (5 / 96)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 3)), (33, (-1 / 2))]

def value369 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 48)), (3, (1 / 2)), (12, (1 / 3)), (13, (2 / 3)), (34, (1 / 6))]

def value370 : Sparse (Fin 909) := [(3, (1 / 6)), (26, (1 / 6)), (34, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (60, (1 / 6)), (67, (1 / 6)), (275, (-1 / 2)), (276, (1 / 6))]

def value371 : Sparse (Fin 909) := [(3, (1 / 2)), (4, (1 / 6)), (13, (1 / 6)), (26, (1 / 2)), (34, (1 / 3)), (35, (1 / 6)), (67, (1 / 6))]

def value372 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 3))]

def value373 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 3)), (65, (-1 / 2)), (67, (1 / 6))]

def value374 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 48)), (2, (7 / 96)), (3, (1 / 3)), (26, (1 / 6)), (33, (-1 / 2))]

def value375 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (26, (1 / 2)), (34, (1 / 3)), (66, (-1 / 2)), (67, (1 / 6))]

def value376 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (3, (2 / 3)), (4, (1 / 3)), (26, (1 / 2)), (34, (1 / 6))]

def value377 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 2)), (4, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (34, (1 / 6))]

def value378 : Sparse (Fin 909) := [(3, (1 / 2)), (12, (1 / 6)), (13, (1 / 2)), (26, (1 / 6)), (34, (1 / 3)), (35, (1 / 6)), (60, (1 / 6))]

def value379 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (55, (-1 / 2)), (61, (-1 / 2))]

def value380 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (1 / 8)), (2, (7 / 24)), (5, (-1 / 1)), (6, (1 / 8)), (9, (-1 / 6)), (27, (3 / 2)), (68, (5 / 2))]

def value381 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-1 / 12)), (2, (1 / 6)), (5, (-2 / 3)), (6, (-1 / 6)), (9, (-1 / 3)), (58, (1 / 24)), (68, (1 / 2))]

def value382 : Sparse (Fin 909) := [(0, (-1 / 60)), (1, (-1 / 6)), (2, (-1 / 12)), (5, (-1 / 6)), (6, (1 / 6)), (9, (-1 / 3)), (27, (1 / 2)), (68, (1 / 1))]

def value383 : Sparse (Fin 909) := [(0, (7 / 120)), (1, (-3 / 4)), (2, (-1 / 3)), (5, (-1 / 2)), (6, (1 / 8))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3200 : Sparse (Fin 909) := [(0, (7 / 180)), (1, (-17 / 36)), (2, (1 / 24)), (3, (4 / 9)), (4, (2 / 3)), (12, (2 / 9)), (17, (1 / 2)), (22, (1 / 2)), (24, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 3))]

def value3201 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 12)), (2, (1 / 16)), (3, (5 / 6)), (4, (1 / 3)), (5, (-1 / 24)), (7, (5 / 9)), (12, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (7 / 18)), (27, (1 / 24)), (35, (5 / 18)), (51, (-1 / 6)), (54, (-1 / 6)), (55, (-1 / 3)), (64, (-1 / 3)), (104, (1 / 2))]

def value3202 : Sparse (Fin 909) := [(1, (-7 / 72)), (2, (1 / 12)), (3, (25 / 18)), (4, (1 / 2)), (5, (-1 / 24)), (7, (7 / 18)), (11, (1 / 9)), (26, (7 / 9)), (35, (11 / 18)), (52, (2 / 9)), (67, (1 / 18)), (81, (-1 / 2)), (85, (1 / 1)), (228, (-5 / 6)), (460, (1 / 2)), (709, (1 / 2))]

def value3203 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-23 / 144)), (2, (5 / 72)), (3, (17 / 18)), (4, (5 / 9)), (26, (7 / 9)), (53, (1 / 2))]

def value3204 : Sparse (Fin 909) := [(0, (49 / 1440)), (1, (-13 / 48)), (2, (11 / 288)), (3, (1 / 3)), (4, (5 / 9)), (25, (-1 / 6)), (26, (1 / 18)), (31, (-1 / 2)), (44, (1 / 2)), (45, (1 / 2))]

def value3205 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-13 / 72)), (2, (5 / 144)), (3, (5 / 9)), (4, (1 / 9)), (12, (1 / 9)), (21, (1 / 2)), (31, (-1 / 6))]

def value3206 : Sparse (Fin 909) := [(0, (13 / 480)), (1, (-49 / 96)), (2, (1 / 36)), (3, (7 / 9)), (4, (2 / 3)), (12, (11 / 18)), (22, (1 / 2)), (31, (-1 / 6))]

def value3207 : Sparse (Fin 909) := [(0, (17 / 720)), (1, (-25 / 144)), (2, (1 / 36)), (3, (4 / 9)), (4, (-1 / 6)), (12, (1 / 9)), (18, (1 / 2)), (25, (-1 / 6))]

def value3208 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-55 / 144)), (2, (1 / 36)), (3, (1 / 3)), (4, (2 / 3)), (12, (1 / 9)), (25, (-1 / 6)), (31, (-1 / 3))]

def value3209 : Sparse (Fin 909) := [(0, (7 / 180)), (1, (-13 / 48)), (2, (1 / 144)), (3, (2 / 9)), (4, (2 / 9)), (12, (1 / 18)), (22, (1 / 2)), (31, (-1 / 3))]

def value3210 : Sparse (Fin 909) := [(0, (1 / 48)), (1, (-95 / 288)), (2, (1 / 96)), (3, (5 / 6)), (4, (5 / 9)), (12, (7 / 18)), (21, (1 / 2))]

def value3211 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-25 / 96)), (2, (1 / 72)), (3, (17 / 18)), (4, (1 / 2)), (7, (1 / 18)), (12, (11 / 18)), (13, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (1 / 18)), (33, (-1 / 6)), (35, (1 / 18)), (48, (1 / 2)), (50, (3 / 2)), (55, (-1 / 3)), (113, (1 / 2)), (177, (1 / 2))]

def value3212 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-53 / 288)), (2, (1 / 72)), (3, (13 / 18)), (4, (4 / 9)), (7, (1 / 18)), (12, (5 / 18)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 6)), (26, (5 / 18)), (35, (1 / 18)), (43, (1 / 1)), (44, (1 / 2)), (47, (1 / 2)), (55, (-1 / 3)), (113, (1 / 2)), (114, (1 / 1)), (191, (1 / 2))]

def value3213 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-23 / 288)), (2, (1 / 36)), (3, (2 / 3)), (4, (5 / 18)), (5, (-1 / 72)), (7, (5 / 18)), (11, (1 / 18)), (26, (5 / 9)), (35, (7 / 18)), (52, (1 / 9)), (53, (1 / 1)), (81, (-1 / 3)), (83, (1 / 2)), (84, (3 / 2)), (228, (-2 / 3)), (702, (1 / 1)), (709, (1 / 1))]

def value3214 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-19 / 96)), (2, (1 / 72)), (3, (8 / 9)), (4, (1 / 3)), (7, (1 / 18)), (12, (4 / 9)), (13, (1 / 6)), (18, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 18)), (33, (-1 / 6)), (35, (1 / 18)), (47, (1 / 2)), (55, (-1 / 2)), (177, (1 / 2))]

def value3215 : Sparse (Fin 909) := [(0, (11 / 720)), (1, (-31 / 144)), (2, (1 / 36)), (3, (7 / 6)), (4, (2 / 3)), (7, (1 / 18)), (12, (1 / 6)), (21, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (4 / 9)), (35, (1 / 18)), (44, (1 / 1)), (48, (1 / 2)), (55, (-1 / 2)), (191, (1 / 2))]

def value3216 : Sparse (Fin 909) := [(0, (19 / 720)), (1, (-61 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (4 / 9)), (12, (2 / 9)), (22, (1 / 2))]

def value3217 : Sparse (Fin 909) := [(0, (19 / 480)), (1, (-13 / 36)), (2, (1 / 288)), (3, (11 / 18)), (4, (5 / 18)), (12, (1 / 6)), (18, (1 / 2))]

def value3218 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (13 / 288)), (2, (-1 / 96)), (3, (1 / 9)), (5, (-11 / 72)), (6, (5 / 288)), (7, (1 / 18)), (9, (-1 / 72)), (13, (1 / 2)), (35, (13 / 18)), (52, (4 / 9)), (60, (7 / 18)), (68, (1 / 24)), (70, (1 / 18)), (82, (2 / 9)), (125, (-1 / 6)), (128, (5 / 18)), (260, (-1 / 3)), (309, (-1 / 3)), (323, (1 / 2)), (728, (-1 / 6))]

def value3219 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 48)), (2, (11 / 288)), (3, (11 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 9)), (12, (1 / 9)), (13, (7 / 18)), (26, (2 / 9)), (34, (1 / 6)), (35, (1 / 6)), (51, (-1 / 3)), (52, (1 / 9)), (71, (1 / 18)), (138, (1 / 2)), (146, (1 / 2)), (197, (-1 / 3)), (236, (-1 / 6)), (400, (1 / 1)), (810, (1 / 1))]

def value3220 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (-1 / 144)), (2, (7 / 96)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 9)), (12, (2 / 9)), (13, (2 / 9)), (23, (-1 / 6)), (33, (-1 / 6)), (51, (-1 / 1)), (52, (1 / 9)), (55, (-1 / 6)), (69, (1 / 18)), (124, (-1 / 6)), (125, (-1 / 6)), (126, (-1 / 6)), (140, (1 / 2)), (142, (1 / 1)), (145, (1 / 2)), (383, (1 / 1)), (538, (1 / 1))]

def value3221 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 288)), (2, (1 / 12)), (3, (5 / 9)), (5, (-11 / 72)), (6, (5 / 288)), (7, (1 / 6)), (9, (-1 / 72)), (12, (1 / 9)), (13, (2 / 9)), (23, (-1 / 6)), (26, (1 / 9)), (27, (1 / 8)), (35, (1 / 6)), (51, (-2 / 3)), (52, (2 / 9)), (54, (-1 / 3)), (55, (-1 / 3)), (64, (-1 / 1)), (68, (1 / 12)), (70, (1 / 18)), (125, (-1 / 3)), (238, (-2 / 3)), (260, (-1 / 3)), (309, (-1 / 3))]

def value3222 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 16)), (2, (37 / 288)), (3, (5 / 18)), (5, (-23 / 72)), (6, (1 / 32)), (7, (7 / 18)), (8, (5 / 18)), (9, (-1 / 36)), (24, (-1 / 6)), (27, (1 / 24)), (35, (2 / 9)), (51, (-1 / 6)), (52, (7 / 18)), (68, (1 / 24)), (69, (1 / 3)), (70, (1 / 6)), (71, (5 / 18)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (262, (-1 / 3)), (308, (-1 / 6)), (309, (-1 / 6)), (322, (1 / 2)), (327, (1 / 2))]

def value3223 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 24)), (2, (13 / 288)), (3, (1 / 3)), (5, (-7 / 72)), (6, (1 / 96)), (7, (1 / 3)), (9, (-1 / 72)), (12, (1 / 6)), (23, (-1 / 2)), (27, (1 / 8)), (35, (1 / 9)), (51, (-1 / 1)), (54, (-1 / 1)), (68, (1 / 24)), (69, (1 / 6)), (70, (1 / 9)), (124, (-1 / 2)), (196, (-1 / 3)), (259, (-1 / 1)), (282, (3 / 2)), (308, (-1 / 2)), (723, (-1 / 2))]

def value3224 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 16)), (2, (5 / 24)), (3, (4 / 9)), (4, (1 / 6)), (5, (-7 / 36)), (6, (1 / 144)), (7, (1 / 3)), (8, (4 / 9)), (31, (-2 / 3)), (35, (1 / 9)), (51, (-2 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (107, (1 / 1)), (238, (-1 / 2))]

def value3225 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-7 / 288)), (2, (5 / 72)), (3, (4 / 9)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (12, (1 / 18)), (13, (1 / 18)), (26, (2 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (43, (1 / 2)), (51, (-1 / 6)), (77, (1 / 2)), (97, (1 / 1)), (107, (1 / 2)), (238, (-1 / 3)), (737, (1 / 2))]

def value3226 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (11 / 288)), (2, (29 / 288)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 8)), (6, (1 / 72)), (7, (1 / 18)), (8, (2 / 9)), (9, (-1 / 72)), (26, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9)), (56, (-1 / 2)), (69, (1 / 18)), (71, (1 / 18)), (228, (-1 / 3)), (262, (-1 / 3)), (735, (1 / 2)), (796, (-1 / 6))]

def value3227 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (19 / 144)), (3, (5 / 18)), (4, (1 / 9)), (5, (-11 / 72)), (6, (1 / 288)), (7, (1 / 6)), (8, (4 / 9)), (31, (-1 / 6)), (51, (-2 / 3)), (56, (-1 / 3)), (71, (1 / 9)), (107, (1 / 2)), (238, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2))]

def value3228 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (1 / 12)), (3, (1 / 2)), (4, (1 / 18)), (5, (-1 / 8)), (6, (1 / 288)), (7, (1 / 3)), (8, (5 / 18)), (26, (1 / 9)), (35, (1 / 6)), (51, (-5 / 6)), (56, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (71, (1 / 18)), (77, (1 / 1)), (97, (1 / 2)), (238, (-1 / 6)), (286, (1 / 2)), (309, (-1 / 6)), (736, (1 / 2))]

def value3229 : Sparse (Fin 909) := [(1, (-11 / 144)), (2, (11 / 144)), (3, (11 / 18)), (4, (1 / 9)), (5, (-1 / 18)), (7, (4 / 9)), (24, (-2 / 3)), (26, (1 / 9)), (27, (1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3))]

def value3230 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-1 / 9)), (2, (25 / 288)), (3, (11 / 18)), (4, (7 / 18)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 9)), (26, (2 / 9)), (31, (-2 / 3)), (35, (1 / 9)), (51, (-2 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (107, (1 / 1)), (238, (-1 / 2))]

def value3231 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (5 / 144)), (3, (7 / 18)), (4, (1 / 6)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 6)), (8, (1 / 18)), (26, (1 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (46, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (56, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (107, (1 / 2)), (238, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (735, (1 / 2)), (736, (1 / 2))]

def value3232 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-37 / 288)), (2, (5 / 36)), (3, (13 / 18)), (4, (1 / 6)), (5, (-5 / 36)), (6, (1 / 144)), (7, (7 / 18)), (8, (2 / 9)), (24, (-1 / 3)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (68, (1 / 24)), (107, (1 / 2)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (238, (-1 / 6))]

def value3233 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-13 / 144)), (2, (7 / 72)), (3, (2 / 3)), (4, (1 / 6)), (5, (-7 / 72)), (6, (1 / 96)), (7, (5 / 18)), (8, (1 / 9)), (12, (1 / 18)), (13, (1 / 18)), (24, (-1 / 6)), (26, (1 / 18)), (27, (1 / 24)), (31, (-1 / 3)), (35, (1 / 9)), (46, (1 / 2)), (51, (-1 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (95, (1 / 2)), (106, (1 / 2)), (237, (-1 / 6)), (735, (1 / 1)), (736, (1 / 2)), (738, (1 / 2))]

def value3234 : Sparse (Fin 909) := [(1, (-11 / 96)), (2, (37 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-1 / 9)), (6, (1 / 144)), (7, (1 / 3)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (24, (-1 / 3)), (26, (1 / 6)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 6)), (35, (1 / 6)), (51, (-1 / 2)), (52, (1 / 18)), (55, (-1 / 6)), (95, (1 / 2)), (107, (1 / 2)), (238, (-1 / 6))]

def value3235 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 72)), (2, (11 / 96)), (3, (2 / 9)), (4, (1 / 9)), (5, (-1 / 8)), (6, (1 / 96)), (8, (1 / 6)), (9, (-1 / 72)), (24, (-1 / 6)), (27, (1 / 6)), (31, (-1 / 3)), (51, (-1 / 1)), (52, (1 / 9)), (56, (-1 / 3)), (68, (1 / 12)), (71, (1 / 18)), (126, (-1 / 3)), (238, (-1 / 3)), (262, (-1 / 3)), (308, (-1 / 6)), (309, (-1 / 6))]

def value3236 : Sparse (Fin 909) := [(0, (1 / 480)), (2, (3 / 32)), (3, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (8, (1 / 3)), (12, (1 / 18)), (27, (1 / 24)), (30, (-1 / 6)), (45, (1 / 2)), (51, (-1 / 2)), (54, (-1 / 6)), (71, (1 / 9)), (259, (-1 / 6)), (308, (-1 / 6)), (325, (1 / 2)), (738, (1 / 2)), (739, (1 / 2))]

def value3237 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 48)), (2, (13 / 288)), (3, (1 / 6)), (5, (-11 / 72)), (6, (1 / 48)), (8, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (33, (-1 / 3)), (51, (-1 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (71, (1 / 9)), (259, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 6)), (739, (1 / 1))]

def value3238 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (-1 / 144)), (2, (17 / 288)), (3, (1 / 6)), (5, (-5 / 36)), (6, (1 / 144)), (7, (5 / 18)), (8, (1 / 3)), (12, (1 / 18)), (23, (-1 / 6)), (27, (1 / 8)), (51, (-2 / 3)), (54, (-1 / 3)), (69, (1 / 18)), (71, (1 / 9)), (282, (1 / 2)), (293, (1 / 1)), (308, (-1 / 6)), (738, (1 / 1))]

def value3239 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (11 / 144)), (2, (1 / 16)), (3, (1 / 9)), (5, (-17 / 72)), (6, (1 / 24)), (7, (1 / 9)), (9, (-1 / 24)), (13, (1 / 3)), (23, (-1 / 6)), (27, (1 / 24)), (35, (4 / 9)), (52, (2 / 9)), (54, (-1 / 3)), (63, (-1 / 3)), (68, (1 / 12)), (70, (1 / 9)), (196, (-1 / 3)), (237, (-1 / 3)), (721, (-1 / 3)), (723, (-1 / 6))]

def value3240 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-11 / 72)), (2, (13 / 144)), (3, (5 / 6)), (5, (-1 / 18)), (7, (1 / 3)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 1)), (27, (1 / 4)), (35, (1 / 9)), (51, (-1 / 1)), (54, (-1 / 1)), (68, (1 / 24)), (124, (-1 / 2)), (196, (-1 / 3))]

def value3241 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-31 / 288)), (2, (1 / 48)), (3, (5 / 6)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 2)), (13, (1 / 9)), (23, (-1 / 2)), (25, (-1 / 2)), (27, (1 / 24)), (33, (-1 / 1)), (35, (1 / 9)), (51, (-1 / 2)), (54, (-1 / 1)), (63, (-1 / 3)), (293, (3 / 2)), (721, (-1 / 2))]

def value3242 : Sparse (Fin 909) := [(0, (5 / 288)), (1, (-1 / 18)), (2, (55 / 288)), (3, (1 / 9)), (5, (-1 / 6)), (6, (1 / 144)), (7, (1 / 9)), (8, (5 / 9)), (27, (1 / 6)), (30, (-2 / 3)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (236, (-2 / 3))]

def value3243 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-25 / 144)), (2, (1 / 12)), (3, (7 / 9)), (4, (1 / 2)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 3)), (26, (1 / 9)), (27, (1 / 8)), (31, (-1 / 3)), (35, (1 / 9)), (51, (-4 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-5 / 6)), (97, (1 / 2)), (238, (-1 / 6))]

def value3244 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 36)), (2, (3 / 32)), (3, (1 / 2)), (5, (-1 / 6)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 3)), (27, (1 / 12)), (35, (1 / 9)), (51, (-1 / 3)), (54, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 3)), (196, (-1 / 6)), (236, (-1 / 3))]

def value3245 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 144)), (2, (13 / 96)), (3, (13 / 18)), (4, (5 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (7, (1 / 6)), (8, (2 / 9)), (9, (-1 / 72)), (26, (2 / 9)), (35, (2 / 9)), (52, (4 / 9)), (56, (-1 / 3)), (69, (1 / 18)), (81, (-5 / 6)), (228, (-2 / 3)), (501, (1 / 2)), (796, (-1 / 6))]

def value3246 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-1 / 24)), (2, (5 / 36)), (3, (2 / 3)), (4, (7 / 18)), (5, (-5 / 36)), (6, (1 / 288)), (7, (1 / 6)), (8, (7 / 18)), (24, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (51, (-1 / 3)), (56, (-2 / 3)), (71, (1 / 18)), (107, (1 / 1)), (126, (-1 / 6)), (262, (-1 / 6)), (753, (1 / 2))]

def value3247 : Sparse (Fin 909) := [(0, (1 / 36)), (1, (-55 / 288)), (2, (25 / 288)), (3, (7 / 18)), (4, (4 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 18)), (31, (-2 / 3)), (49, (1 / 2)), (51, (-1 / 3)), (107, (1 / 2)), (238, (-1 / 6))]

def value3248 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-3 / 16)), (2, (1 / 16)), (3, (2 / 3)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 18)), (12, (1 / 3)), (13, (1 / 18)), (26, (1 / 9)), (31, (-1 / 2)), (35, (1 / 18)), (43, (1 / 1)), (47, (1 / 2)), (51, (-1 / 6)), (97, (1 / 2)), (204, (1 / 2)), (238, (-1 / 6))]

def value3249 : Sparse (Fin 909) := [(1, (-1 / 12)), (2, (7 / 96)), (3, (5 / 6)), (4, (7 / 18)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 6)), (26, (1 / 6)), (27, (1 / 24)), (31, (-1 / 6)), (46, (1 / 1)), (51, (-2 / 3)), (52, (1 / 9)), (56, (-1 / 3)), (69, (1 / 18)), (124, (-1 / 6)), (262, (-1 / 6)), (735, (1 / 1)), (745, (1 / 1)), (753, (1 / 2))]

def value3250 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (-49 / 288)), (2, (5 / 288)), (3, (1 / 2)), (4, (7 / 18)), (7, (1 / 18)), (12, (1 / 9)), (13, (1 / 18)), (22, (1 / 2)), (26, (1 / 9)), (31, (-1 / 2)), (35, (1 / 18)), (46, (1 / 2)), (49, (1 / 2)), (51, (-1 / 3)), (107, (1 / 2)), (204, (1 / 2)), (238, (-1 / 6))]

def value3251 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-1 / 8)), (2, (25 / 288)), (3, (17 / 18)), (4, (1 / 6)), (5, (-5 / 72)), (6, (1 / 144)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 3)), (13, (2 / 9)), (24, (-1 / 6)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 3)), (52, (1 / 9)), (55, (-1 / 3)), (68, (1 / 24)), (126, (-1 / 6)), (146, (1 / 2)), (197, (-1 / 6)), (204, (1 / 2)), (237, (-1 / 6)), (238, (-1 / 6))]

def value3252 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-37 / 288)), (2, (23 / 288)), (3, (1 / 1)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (12, (7 / 18)), (13, (5 / 9)), (26, (1 / 6)), (27, (1 / 12)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 6)), (51, (-1 / 2)), (52, (1 / 9)), (55, (-1 / 3)), (204, (1 / 2)), (238, (-1 / 6))]

def value3253 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-43 / 288)), (2, (11 / 144)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (31, (-1 / 3)), (47, (1 / 2)), (51, (-2 / 3)), (52, (1 / 18)), (69, (1 / 18)), (124, (-1 / 6)), (126, (-1 / 3)), (205, (1 / 2)), (207, (1 / 2)), (209, (1 / 2)), (538, (1 / 2)), (751, (1 / 2)), (753, (1 / 1))]

def value3254 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 144)), (2, (-1 / 144)), (3, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 6)), (13, (1 / 3)), (35, (2 / 9)), (52, (4 / 9)), (54, (-1 / 3)), (63, (-1 / 6)), (69, (1 / 6)), (123, (-1 / 3)), (124, (-1 / 6)), (125, (-1 / 3)), (126, (-1 / 6)), (129, (1 / 2)), (144, (1 / 2)), (306, (-1 / 6)), (498, (1 / 2))]

def value3255 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 48)), (2, (7 / 144)), (3, (1 / 9)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 9)), (9, (-1 / 72)), (12, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 12)), (51, (-1 / 3)), (68, (1 / 8)), (69, (1 / 18)), (124, (-1 / 6)), (126, (-1 / 3)), (308, (-1 / 6)), (751, (1 / 2))]

def value3256 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 24)), (2, (3 / 32)), (3, (5 / 18)), (5, (-5 / 24)), (6, (1 / 24)), (7, (1 / 18)), (9, (-1 / 72)), (12, (1 / 18)), (33, (-2 / 3)), (35, (2 / 9)), (52, (4 / 9)), (54, (-1 / 3)), (69, (1 / 18)), (306, (-1 / 2)), (498, (1 / 2)), (721, (-2 / 3)), (723, (-1 / 6)), (760, (1 / 1))]

def value3257 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (7 / 288)), (2, (11 / 288)), (3, (5 / 18)), (4, (1 / 18)), (5, (-1 / 24)), (7, (1 / 18)), (12, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (51, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 6)), (205, (1 / 2))]

def value3258 : Sparse (Fin 909) := [(1, (-5 / 72)), (2, (1 / 36)), (3, (5 / 9)), (4, (1 / 18)), (7, (1 / 9)), (12, (7 / 18)), (13, (1 / 6)), (15, (1 / 2)), (23, (-1 / 2)), (25, (-1 / 3)), (27, (1 / 24)), (33, (-1 / 3)), (35, (1 / 18)), (51, (-1 / 6)), (54, (-1 / 3)), (63, (-1 / 6)), (124, (-1 / 6)), (144, (1 / 2)), (196, (-1 / 6)), (205, (1 / 2))]

def value3259 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-13 / 72)), (2, (1 / 9)), (3, (2 / 9)), (4, (5 / 18)), (5, (-1 / 18)), (8, (1 / 9)), (24, (-1 / 3)), (27, (1 / 6)), (31, (-1 / 2)), (51, (-2 / 3)), (68, (1 / 24)), (126, (-1 / 3)), (207, (1 / 2)), (238, (-1 / 6))]

def value3260 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-5 / 32)), (2, (7 / 72)), (3, (5 / 9)), (4, (7 / 18)), (5, (-1 / 18)), (6, (1 / 288)), (12, (1 / 9)), (27, (1 / 6)), (31, (-1 / 2)), (51, (-1 / 1)), (52, (1 / 9)), (209, (1 / 2)), (238, (-1 / 6))]

def value3261 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-43 / 288)), (2, (1 / 48)), (3, (7 / 9)), (4, (1 / 2)), (12, (1 / 6)), (21, (1 / 2)), (26, (2 / 9)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (1 / 18)), (51, (-1 / 2)), (52, (1 / 18)), (54, (-1 / 6)), (56, (-1 / 3)), (191, (1 / 2)), (209, (1 / 2))]

def value3262 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-13 / 72)), (2, (13 / 288)), (3, (17 / 18)), (4, (4 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 3)), (23, (-1 / 3)), (24, (-1 / 3)), (25, (-1 / 6)), (26, (1 / 6)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (1 / 18)), (43, (1 / 2)), (47, (1 / 1)), (48, (1 / 2)), (51, (-1 / 6)), (54, (-1 / 6)), (56, (-1 / 6)), (97, (1 / 2)), (191, (1 / 2))]

def value3263 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (7 / 288)), (2, (7 / 144)), (3, (11 / 18)), (5, (-5 / 72)), (6, (1 / 72)), (12, (1 / 6)), (13, (2 / 3)), (23, (-1 / 6)), (27, (1 / 24)), (33, (-1 / 3)), (35, (1 / 9)), (52, (2 / 9)), (54, (-1 / 6)), (63, (-1 / 3)), (68, (1 / 24)), (126, (-1 / 6)), (144, (1 / 2)), (196, (-1 / 6)), (237, (-1 / 3))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3264 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 24)), (2, (5 / 288)), (3, (5 / 9)), (5, (-1 / 9)), (6, (1 / 36)), (12, (1 / 9)), (13, (7 / 9)), (25, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (35, (2 / 9)), (52, (1 / 3)), (63, (-1 / 2)), (123, (-1 / 6)), (231, (1 / 2)), (237, (-1 / 3)), (306, (-1 / 6)), (721, (-1 / 6)), (760, (1 / 2))]

def value3265 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-35 / 288)), (2, (5 / 144)), (3, (5 / 6)), (4, (1 / 3)), (12, (1 / 2)), (13, (2 / 9)), (23, (-1 / 2)), (24, (-1 / 2)), (25, (-1 / 2)), (27, (1 / 24)), (33, (-1 / 1)), (55, (-1 / 1)), (63, (-1 / 3)), (299, (3 / 2)), (306, (-1 / 2))]

def value3266 : Sparse (Fin 909) := [(0, (29 / 720)), (1, (-79 / 288)), (2, (31 / 288)), (3, (5 / 18)), (4, (2 / 9)), (5, (-1 / 72)), (12, (1 / 18)), (20, (1 / 1)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 3)), (51, (-1 / 6)), (52, (1 / 18)), (126, (-1 / 6)), (205, (1 / 2)), (208, (2 / 1))]

def value3267 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-1 / 9)), (2, (17 / 288)), (3, (5 / 9)), (4, (1 / 9)), (5, (-1 / 36)), (12, (1 / 3)), (13, (1 / 9)), (15, (1 / 2)), (23, (-1 / 6)), (24, (-1 / 6)), (27, (1 / 8)), (51, (-1 / 3)), (52, (1 / 9)), (126, (-1 / 6)), (144, (1 / 2)), (205, (1 / 1)), (208, (1 / 1))]

def value3268 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-19 / 96)), (2, (7 / 288)), (3, (11 / 9)), (4, (4 / 9)), (7, (1 / 18)), (12, (1 / 2)), (13, (1 / 6)), (18, (1 / 2)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-1 / 3)), (26, (5 / 18)), (33, (-1 / 3)), (35, (1 / 18)), (43, (1 / 1)), (47, (1 / 2)), (55, (-1 / 3)), (63, (-1 / 6)), (143, (1 / 2))]

def value3269 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (11 / 288)), (2, (29 / 288)), (3, (11 / 18)), (5, (-1 / 4)), (6, (1 / 32)), (7, (1 / 3)), (8, (1 / 6)), (11, (1 / 9)), (13, (1 / 18)), (26, (1 / 6)), (35, (11 / 18)), (51, (-1 / 6)), (52, (11 / 18)), (59, (-1 / 3)), (85, (1 / 2)), (103, (1 / 2)), (123, (-1 / 6)), (128, (1 / 18)), (228, (-2 / 3)), (315, (1 / 2)), (545, (1 / 2)), (721, (-1 / 6))]

def value3270 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (23 / 288)), (2, (17 / 144)), (3, (7 / 18)), (5, (-2 / 9)), (6, (1 / 36)), (7, (1 / 6)), (8, (2 / 9)), (12, (1 / 9)), (13, (7 / 18)), (26, (1 / 9)), (35, (5 / 18)), (52, (2 / 9)), (54, (-1 / 6)), (59, (-1 / 6)), (82, (1 / 18)), (85, (1 / 1)), (199, (-1 / 6)), (228, (-1 / 3)), (329, (1 / 1)), (540, (1 / 2)), (728, (-1 / 6)), (794, (1 / 1))]

def value3271 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 48)), (2, (11 / 72)), (3, (8 / 9)), (4, (2 / 9)), (5, (-1 / 4)), (6, (1 / 48)), (7, (5 / 9)), (8, (5 / 18)), (11, (1 / 9)), (26, (7 / 18)), (35, (13 / 18)), (52, (4 / 9)), (81, (-1 / 2)), (84, (1 / 2)), (85, (1 / 1)), (228, (-5 / 6))]

def value3272 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (19 / 288)), (2, (1 / 9)), (3, (4 / 9)), (4, (1 / 18)), (5, (-19 / 72)), (6, (5 / 144)), (7, (7 / 18)), (8, (1 / 6)), (11, (1 / 9)), (26, (1 / 6)), (33, (-1 / 6)), (35, (5 / 9)), (51, (-1 / 6)), (52, (7 / 18)), (69, (1 / 18)), (70, (1 / 18)), (81, (-1 / 6)), (85, (1 / 2)), (228, (-2 / 3)), (259, (-1 / 6)), (306, (-1 / 6)), (308, (-1 / 6)), (315, (1 / 2)), (322, (1 / 2)), (517, (1 / 2)), (721, (-1 / 6))]

def value3273 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (7 / 96)), (3, (5 / 18)), (4, (1 / 18)), (5, (-13 / 72)), (6, (5 / 288)), (7, (1 / 9)), (8, (1 / 6)), (11, (1 / 18)), (26, (1 / 9)), (35, (5 / 18)), (39, (1 / 2)), (52, (7 / 18)), (55, (-1 / 6)), (81, (-1 / 6)), (85, (1 / 2)), (228, (-1 / 3)), (306, (-1 / 6)), (329, (1 / 1)), (500, (1 / 2)), (541, (1 / 2)), (728, (-1 / 6)), (764, (1 / 2)), (794, (1 / 2))]

def value3274 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 288)), (2, (3 / 32)), (3, (13 / 18)), (4, (2 / 9)), (5, (-13 / 72)), (6, (1 / 36)), (7, (2 / 9)), (11, (1 / 9)), (26, (1 / 3)), (31, (-1 / 6)), (33, (-1 / 6)), (35, (11 / 18)), (52, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (99, (1 / 2)), (123, (-1 / 6)), (228, (-2 / 3)), (237, (-1 / 6)), (306, (-1 / 6)), (315, (1 / 2)), (517, (1 / 2)), (721, (-1 / 6))]

def value3275 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-31 / 288)), (2, (7 / 96)), (3, (17 / 18)), (4, (1 / 3)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 6)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 6)), (24, (-1 / 6)), (26, (1 / 3)), (27, (1 / 24)), (31, (-1 / 6)), (35, (1 / 3)), (51, (-1 / 2)), (52, (1 / 3)), (56, (-1 / 3)), (99, (1 / 2)), (103, (1 / 2)), (123, (-1 / 3)), (237, (-1 / 6))]

def value3276 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 32)), (2, (23 / 288)), (3, (11 / 18)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 48)), (7, (1 / 18)), (8, (1 / 18)), (12, (1 / 9)), (13, (4 / 9)), (26, (1 / 9)), (35, (5 / 18)), (40, (1 / 2)), (52, (1 / 3)), (55, (-1 / 6)), (56, (-1 / 6)), (81, (-1 / 6)), (82, (1 / 18)), (85, (1 / 2)), (128, (1 / 18)), (201, (-1 / 6)), (228, (-1 / 6)), (306, (-1 / 6)), (329, (1 / 2)), (541, (1 / 2)), (728, (-1 / 6)), (760, (1 / 2)), (794, (3 / 2))]

def value3277 : Sparse (Fin 909) := [(1, (-5 / 72)), (2, (1 / 9)), (3, (13 / 9)), (4, (1 / 2)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 3)), (11, (1 / 9)), (26, (7 / 9)), (35, (5 / 9)), (52, (1 / 3)), (81, (-2 / 3)), (83, (1 / 2)), (85, (1 / 1)), (228, (-1 / 1))]

def value3278 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (-1 / 32)), (3, (13 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (23, (-1 / 6)), (25, (-1 / 2)), (26, (7 / 18)), (33, (-1 / 6)), (35, (1 / 9)), (51, (-1 / 6)), (54, (-1 / 3)), (56, (-1 / 6)), (97, (1 / 2)), (123, (-1 / 6)), (124, (-1 / 6)), (137, (1 / 2)), (197, (-1 / 6)), (216, (1 / 2)), (217, (1 / 2))]

def value3279 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 288)), (2, (-5 / 144)), (3, (2 / 3)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 6)), (8, (1 / 18)), (13, (1 / 6)), (23, (-1 / 6)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (7 / 18)), (35, (1 / 6)), (36, (1 / 2)), (39, (1 / 2)), (54, (-1 / 1)), (56, (-1 / 6)), (97, (1 / 2)), (217, (1 / 2))]

def value3280 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-19 / 288)), (2, (17 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 36)), (6, (1 / 288)), (8, (1 / 9)), (12, (1 / 9)), (13, (1 / 6)), (17, (1 / 2)), (24, (-1 / 3)), (26, (1 / 18)), (35, (1 / 18)), (39, (1 / 1)), (42, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (99, (1 / 2)), (126, (-1 / 6)), (146, (1 / 2)), (197, (-1 / 6)), (216, (1 / 2))]

def value3281 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-43 / 288)), (2, (1 / 16)), (3, (8 / 9)), (4, (1 / 3)), (12, (5 / 18)), (13, (1 / 6)), (22, (1 / 2)), (26, (1 / 6)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (42, (1 / 1)), (52, (1 / 18)), (55, (-1 / 6)), (99, (1 / 2)), (123, (-1 / 6)), (204, (1 / 2)), (217, (1 / 2)), (237, (-1 / 6))]

def value3282 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-55 / 288)), (2, (1 / 18)), (3, (8 / 9)), (4, (1 / 3)), (12, (5 / 18)), (13, (4 / 9)), (22, (1 / 2)), (25, (-1 / 6)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (42, (1 / 1)), (54, (-1 / 6)), (56, (-1 / 6)), (204, (1 / 2)), (217, (1 / 2))]

def value3283 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-19 / 144)), (2, (7 / 144)), (3, (7 / 6)), (4, (1 / 3)), (12, (4 / 9)), (13, (11 / 18)), (26, (1 / 9)), (33, (-1 / 3)), (35, (1 / 6)), (39, (1 / 2)), (42, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 2))]

def value3284 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-3 / 32)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 36)), (6, (1 / 288)), (7, (2 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 2)), (24, (-1 / 2)), (25, (-1 / 6)), (27, (1 / 8)), (35, (1 / 9)), (48, (1 / 2)), (55, (-1 / 3)), (63, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (124, (-1 / 3)), (126, (-1 / 6)), (196, (-1 / 6)), (197, (-1 / 3)), (643, (1 / 2)), (751, (1 / 2))]

def value3285 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 48)), (2, (-5 / 144)), (3, (1 / 6)), (6, (-1 / 144)), (7, (2 / 9)), (11, (1 / 9)), (26, (1 / 9)), (35, (7 / 18)), (36, (1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (69, (1 / 18)), (70, (1 / 18)), (228, (-1 / 3)), (306, (-1 / 6)), (312, (1 / 1)), (498, (1 / 2)), (728, (-1 / 6)), (783, (1 / 2)), (794, (1 / 1))]

def value3286 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 3)), (4, (1 / 6)), (12, (1 / 6)), (33, (-1 / 1)), (36, (3 / 2)), (54, (-1 / 2)), (55, (-1 / 2)), (306, (-1 / 2)), (312, (3 / 2)), (498, (3 / 2)), (721, (-1 / 2)), (723, (-1 / 6)), (728, (-1 / 6)), (783, (1 / 1))]

def value3287 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-11 / 288)), (3, (2 / 3)), (4, (2 / 9)), (26, (1 / 2)), (37, (3 / 2)), (56, (-1 / 2)), (81, (-1 / 2)), (83, (3 / 2)), (228, (-2 / 3)), (501, (3 / 2)), (784, (1 / 1)), (796, (-1 / 6))]

def value3288 : Sparse (Fin 909) := [(1, (-1 / 36)), (2, (1 / 24)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 36)), (7, (1 / 9)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 3)), (27, (1 / 12)), (55, (-1 / 3)), (68, (1 / 24)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3))]

def value3289 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (11 / 288)), (3, (1 / 2)), (4, (1 / 6)), (7, (1 / 18)), (12, (5 / 18)), (15, (1 / 1)), (23, (-1 / 2)), (24, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 12)), (48, (1 / 2)), (51, (-1 / 6)), (124, (-1 / 6)), (137, (1 / 1)), (205, (1 / 1)), (230, (1 / 2))]

def value3290 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 288)), (2, (5 / 144)), (3, (1 / 2)), (4, (1 / 6)), (5, (-5 / 72)), (6, (1 / 72)), (7, (1 / 18)), (11, (1 / 18)), (26, (1 / 3)), (33, (-1 / 3)), (35, (2 / 9)), (37, (1 / 1)), (52, (1 / 6)), (55, (-1 / 3)), (81, (-1 / 3)), (83, (1 / 2)), (228, (-1 / 2)), (306, (-1 / 3)), (312, (1 / 2)), (517, (1 / 1)), (541, (1 / 1)), (721, (-1 / 6)), (728, (-1 / 6)), (784, (1 / 1))]

def value3291 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-5 / 36)), (2, (5 / 288)), (3, (7 / 9)), (4, (1 / 3)), (5, (-1 / 12)), (6, (1 / 72)), (7, (1 / 9)), (24, (-1 / 3)), (26, (1 / 3)), (27, (1 / 12)), (31, (-1 / 3)), (35, (2 / 9)), (52, (2 / 9)), (68, (1 / 24)), (99, (1 / 1)), (123, (-1 / 3)), (124, (-1 / 6)), (126, (-1 / 3)), (197, (-1 / 3)), (237, (-1 / 3))]

def value3292 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 32)), (2, (5 / 144)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 8)), (6, (1 / 36)), (7, (1 / 18)), (11, (1 / 18)), (26, (1 / 9)), (33, (-1 / 3)), (35, (2 / 9)), (40, (1 / 1)), (52, (1 / 6)), (55, (-1 / 3)), (228, (-1 / 6)), (306, (-1 / 3)), (312, (1 / 2)), (721, (-1 / 6)), (728, (-1 / 6)), (760, (1 / 1)), (794, (2 / 1))]

def value3293 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-5 / 36)), (2, (5 / 96)), (3, (5 / 6)), (4, (1 / 3)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 3)), (13, (1 / 9)), (23, (-1 / 1)), (24, (-1 / 1)), (25, (-1 / 2)), (27, (1 / 6)), (35, (1 / 9)), (55, (-1 / 1)), (63, (-1 / 3))]

def value3294 : Sparse (Fin 909) := [(1, (-35 / 288)), (2, (5 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (23, (-1 / 2)), (24, (-1 / 1)), (27, (1 / 8)), (35, (1 / 9)), (55, (-1 / 1)), (68, (1 / 24)), (124, (-1 / 2)), (126, (-1 / 2)), (196, (-1 / 3)), (197, (-1 / 1)), (290, (3 / 2)), (728, (-1 / 2))]

def value3295 : Sparse (Fin 909) := [(0, (19 / 480)), (1, (-7 / 18)), (2, (1 / 32)), (3, (17 / 18)), (4, (8 / 9)), (12, (1 / 18)), (25, (-2 / 3)), (26, (4 / 9)), (31, (-5 / 6)), (35, (1 / 18)), (44, (1 / 1)), (55, (-1 / 6)), (108, (1 / 2)), (123, (-1 / 6))]

def value3296 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-7 / 72)), (2, (-1 / 72)), (3, (19 / 18)), (4, (7 / 18)), (7, (1 / 9)), (12, (5 / 18)), (13, (1 / 9)), (23, (-1 / 3)), (24, (-1 / 6)), (25, (-1 / 2)), (26, (4 / 9)), (31, (-1 / 6)), (35, (1 / 6)), (44, (1 / 2)), (55, (-1 / 2)), (63, (-1 / 6)), (108, (1 / 2)), (123, (-1 / 6))]

def value3297 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-5 / 144)), (2, (1 / 36)), (3, (7 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (7, (1 / 9)), (12, (1 / 6)), (13, (7 / 18)), (35, (5 / 18)), (42, (1 / 1)), (51, (-1 / 3)), (52, (2 / 9)), (54, (-1 / 6)), (56, (-1 / 3)), (82, (1 / 9)), (128, (1 / 9)), (199, (-1 / 6)), (262, (-1 / 3)), (286, (1 / 2)), (309, (-1 / 6)), (328, (1 / 1)), (506, (1 / 1)), (796, (-1 / 6)), (798, (1 / 1))]

def value3298 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 16)), (2, (1 / 16)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 6)), (6, (1 / 72)), (8, (5 / 18)), (13, (1 / 9)), (24, (-1 / 6)), (26, (1 / 18)), (35, (1 / 9)), (39, (1 / 2)), (52, (2 / 9)), (56, (-1 / 3)), (71, (1 / 9)), (82, (1 / 18)), (99, (1 / 2)), (126, (-1 / 6)), (128, (1 / 18)), (197, (-1 / 6)), (201, (-1 / 6)), (262, (-1 / 6)), (288, (1 / 2)), (329, (1 / 2)), (500, (1 / 1)), (764, (1 / 2)), (796, (-1 / 6)), (798, (1 / 2))]

def value3299 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 288)), (2, (19 / 288)), (3, (13 / 18)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (7, (1 / 9)), (11, (1 / 18)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 3)), (35, (5 / 18)), (40, (1 / 2)), (52, (1 / 6)), (55, (-1 / 6)), (56, (-1 / 6)), (75, (1 / 2)), (81, (-1 / 6)), (85, (1 / 2)), (201, (-1 / 6)), (228, (-1 / 3)), (508, (3 / 2)), (541, (1 / 2)), (794, (1 / 2)), (796, (-1 / 6))]

def value3300 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-11 / 288)), (2, (5 / 96)), (3, (4 / 9)), (4, (1 / 6)), (5, (-1 / 9)), (6, (1 / 288)), (7, (1 / 3)), (8, (2 / 9)), (10, (-1 / 6)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 9)), (35, (2 / 9)), (40, (1 / 1)), (56, (-1 / 3)), (81, (-1 / 6)), (82, (1 / 18)), (85, (1 / 1)), (228, (-1 / 3)), (501, (1 / 2)), (508, (1 / 1)), (794, (1 / 1)), (796, (-1 / 6))]

def value3301 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-2 / 9)), (2, (13 / 288)), (3, (1 / 1)), (4, (2 / 3)), (12, (1 / 6)), (13, (1 / 9)), (26, (7 / 18)), (37, (1 / 2)), (40, (1 / 1)), (56, (-1 / 2))]

def value3302 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-19 / 144)), (2, (7 / 288)), (3, (17 / 18)), (4, (5 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (11, (1 / 18)), (26, (5 / 9)), (35, (5 / 18)), (40, (1 / 1)), (52, (1 / 18)), (55, (-1 / 6)), (56, (-1 / 3)), (81, (-1 / 6)), (85, (1 / 1)), (228, (-1 / 2)), (501, (1 / 2)), (508, (1 / 1)), (794, (1 / 1)), (796, (-1 / 6))]

def value3303 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-13 / 288)), (2, (-1 / 96)), (3, (11 / 18)), (5, (-7 / 36)), (6, (1 / 48)), (7, (1 / 9)), (8, (1 / 18)), (9, (-1 / 72)), (12, (1 / 6)), (13, (1 / 3)), (26, (7 / 18)), (27, (1 / 12)), (35, (5 / 9)), (51, (-1 / 6)), (55, (-1 / 3)), (68, (1 / 12)), (71, (1 / 18)), (82, (1 / 9)), (197, (-1 / 3)), (236, (-1 / 6)), (238, (-1 / 3)), (309, (-1 / 6)), (728, (-1 / 6)), (810, (1 / 2))]

def value3304 : Sparse (Fin 909) := [(0, (-17 / 1440)), (1, (-1 / 144)), (2, (13 / 144)), (3, (5 / 9)), (5, (-7 / 72)), (6, (1 / 288)), (7, (1 / 3)), (8, (5 / 18)), (10, (-1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (27, (1 / 24)), (35, (1 / 18)), (51, (-1 / 3)), (52, (1 / 18)), (55, (-1 / 2)), (69, (1 / 18)), (71, (1 / 18)), (95, (1 / 2)), (124, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 6)), (290, (1 / 2)), (538, (1 / 2)), (811, (1 / 2))]

def value3305 : Sparse (Fin 909) := [(0, (1 / 288)), (1, (-7 / 288)), (2, (5 / 32)), (3, (7 / 18)), (4, (1 / 18)), (5, (-11 / 72)), (6, (1 / 96)), (7, (5 / 18)), (8, (1 / 2)), (24, (-1 / 3)), (26, (1 / 18)), (30, (-1 / 3)), (35, (1 / 18)), (49, (1 / 2)), (71, (1 / 9)), (107, (1 / 1)), (126, (-1 / 3)), (197, (-1 / 6)), (236, (-1 / 2)), (810, (1 / 2)), (811, (1 / 2))]

def value3306 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-7 / 96)), (2, (7 / 96)), (3, (7 / 18)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 18)), (23, (-1 / 6)), (24, (-1 / 3)), (27, (1 / 8)), (31, (-2 / 3)), (47, (1 / 2)), (51, (-1 / 2)), (52, (1 / 9)), (55, (-1 / 6)), (106, (1 / 1)), (237, (-1 / 3)), (308, (-1 / 6)), (538, (1 / 1)), (640, (1 / 2)), (812, (1 / 1))]

def value3307 : Sparse (Fin 909) := [(1, (-1 / 144)), (2, (1 / 16)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (8, (1 / 18)), (9, (-1 / 72)), (24, (-1 / 3)), (27, (1 / 8)), (30, (-1 / 6)), (31, (-1 / 6)), (33, (-1 / 3)), (51, (-1 / 6)), (52, (1 / 18)), (55, (-1 / 2)), (68, (1 / 12)), (71, (1 / 18)), (197, (-1 / 3)), (236, (-1 / 6)), (237, (-1 / 3)), (306, (-1 / 3)), (308, (-1 / 6)), (728, (-1 / 6)), (811, (1 / 2))]

def value3308 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-1 / 16)), (2, (1 / 12)), (3, (1 / 18)), (4, (1 / 18)), (5, (-1 / 18)), (6, (1 / 288)), (8, (2 / 9)), (24, (-1 / 2)), (27, (5 / 24)), (30, (-1 / 2)), (49, (1 / 2)), (55, (-1 / 6)), (71, (1 / 9)), (126, (-1 / 3)), (197, (-1 / 6)), (236, (-1 / 2)), (811, (1 / 2)), (812, (1 / 2))]

def value3309 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 18)), (2, (7 / 96)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6)), (12, (1 / 18)), (23, (-1 / 3)), (24, (-1 / 2)), (27, (1 / 4)), (30, (-1 / 6)), (51, (-1 / 6)), (55, (-1 / 3)), (69, (1 / 18)), (71, (1 / 18)), (105, (1 / 2)), (106, (1 / 2)), (124, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 6)), (290, (1 / 2)), (299, (1 / 1)), (751, (1 / 2)), (812, (1 / 2))]

def value3310 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-31 / 288)), (2, (41 / 288)), (3, (2 / 9)), (4, (1 / 9)), (5, (-1 / 12)), (7, (1 / 9)), (8, (2 / 9)), (23, (-1 / 3)), (24, (-1 / 1)), (27, (5 / 12)), (30, (-2 / 3)), (55, (-1 / 3)), (68, (1 / 24)), (125, (-1 / 6)), (126, (-1 / 3)), (236, (-1 / 3))]

def value3311 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-11 / 96)), (2, (5 / 72)), (3, (1 / 6)), (4, (1 / 6)), (5, (-1 / 24)), (6, (1 / 288)), (8, (1 / 9)), (24, (-2 / 3)), (27, (5 / 24)), (30, (-1 / 3)), (31, (-1 / 6)), (55, (-1 / 3)), (68, (1 / 24)), (106, (1 / 2)), (126, (-1 / 2)), (197, (-1 / 6)), (236, (-1 / 6)), (237, (-1 / 6))]

def value3312 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-1 / 144)), (2, (1 / 96)), (5, (-1 / 72)), (6, (1 / 288)), (23, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 6)), (31, (-1 / 3)), (68, (1 / 24)), (105, (1 / 2)), (124, (-1 / 6)), (236, (-2 / 3)), (237, (-1 / 6))]

def value3313 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-1 / 24)), (2, (1 / 72)), (5, (-1 / 36)), (6, (1 / 144)), (23, (-1 / 3)), (25, (-1 / 3)), (27, (1 / 6)), (30, (-1 / 3)), (31, (-1 / 3)), (63, (-1 / 3)), (68, (1 / 24)), (105, (1 / 1)), (124, (-1 / 3)), (196, (-1 / 6)), (236, (-1 / 3)), (237, (-1 / 3))]

def value3314 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (1 / 144)), (2, (11 / 144)), (3, (1 / 6)), (4, (1 / 18)), (5, (-1 / 6)), (6, (1 / 32)), (7, (1 / 18)), (9, (-1 / 72)), (27, (1 / 12)), (31, (-1 / 3)), (33, (-2 / 3)), (35, (1 / 9)), (51, (-1 / 3)), (52, (2 / 9)), (55, (-1 / 3)), (68, (1 / 24)), (69, (1 / 18)), (123, (-1 / 3)), (124, (-1 / 6)), (237, (-1 / 3)), (259, (-1 / 3)), (306, (-2 / 3)), (308, (-1 / 3)), (312, (1 / 2)), (315, (1 / 1)), (721, (-1 / 2)), (728, (-1 / 6))]

def value3315 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (5 / 96)), (2, (5 / 288)), (5, (-1 / 72)), (17, (1 / 1)), (23, (-1 / 3)), (25, (-1 / 2)), (27, (1 / 8)), (30, (-1 / 3)), (31, (-1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (124, (-1 / 6)), (203, (2 / 1)), (230, (1 / 2))]

def value3316 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 72)), (2, (1 / 144)), (5, (-1 / 36)), (14, (1 / 2)), (23, (-1 / 2)), (25, (-2 / 3)), (27, (1 / 8)), (31, (-1 / 3)), (63, (-1 / 6)), (108, (1 / 1)), (123, (-1 / 3)), (124, (-1 / 6)), (129, (1 / 2)), (203, (1 / 1)), (230, (1 / 1))]

def value3317 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-3 / 16)), (2, (1 / 96)), (23, (-2 / 3)), (25, (-1 / 3)), (27, (-1 / 6)), (68, (1 / 24)), (124, (-1 / 3)), (230, (1 / 2))]

def value3318 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-7 / 144)), (2, (1 / 288)), (14, (1 / 2)), (23, (-1 / 3)), (25, (-1 / 6)), (27, (1 / 12)), (63, (-1 / 2)), (124, (-1 / 6)), (129, (1 / 2)), (196, (-1 / 6)), (230, (1 / 2))]

def value3319 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 288)), (5, (-1 / 72)), (6, (1 / 288)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 24)), (30, (-1 / 3)), (31, (-1 / 6)), (68, (1 / 24)), (123, (-1 / 3)), (124, (-1 / 6)), (203, (1 / 2)), (236, (-1 / 6)), (237, (-1 / 3))]

def value3320 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-2 / 9)), (2, (-1 / 72)), (23, (-1 / 1)), (27, (1 / 12)), (63, (-2 / 3))]

def value3321 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 96)), (2, (5 / 288)), (25, (-1 / 2)), (27, (1 / 12)), (30, (-1 / 6)), (31, (-1 / 2)), (105, (1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (237, (-1 / 6))]

def value3322 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-7 / 144)), (2, (-1 / 96)), (17, (1 / 2)), (23, (-1 / 3)), (25, (-2 / 3)), (27, (1 / 24)), (31, (-2 / 3)), (63, (-1 / 3)), (105, (1 / 2)), (108, (1 / 2)), (123, (-1 / 6)), (231, (1 / 2)), (237, (-1 / 6))]

def value3323 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 32)), (2, (17 / 288)), (3, (7 / 18)), (4, (1 / 18)), (5, (-5 / 36)), (6, (5 / 288)), (7, (1 / 9)), (8, (1 / 9)), (11, (1 / 18)), (12, (1 / 9)), (13, (2 / 9)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 3)), (39, (1 / 2)), (51, (-1 / 6)), (52, (5 / 18)), (54, (-1 / 3)), (56, (-1 / 6)), (59, (-1 / 6)), (74, (1 / 2)), (82, (1 / 18)), (89, (1 / 2)), (123, (-1 / 6)), (128, (1 / 18)), (199, (-1 / 6)), (201, (-1 / 6)), (226, (-1 / 6)), (228, (-1 / 6)), (315, (1 / 2)), (507, (3 / 2)), (540, (1 / 2)), (721, (-1 / 6)), (723, (-1 / 6)), (764, (1 / 2))]

def value3324 : Sparse (Fin 909) := [(1, (-1 / 16)), (2, (-5 / 144)), (3, (1 / 9)), (12, (1 / 9)), (33, (-1 / 3)), (39, (1 / 1)), (51, (-1 / 3)), (54, (-2 / 3)), (259, (-1 / 3)), (282, (1 / 2)), (306, (-1 / 6)), (308, (-1 / 6)), (315, (1 / 1)), (498, (1 / 2)), (507, (1 / 1)), (721, (-1 / 3)), (723, (-1 / 3)), (764, (1 / 1))]

def value3325 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-11 / 288)), (2, (5 / 144)), (3, (5 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 72)), (7, (1 / 18)), (11, (1 / 18)), (12, (1 / 18)), (25, (-1 / 3)), (26, (1 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (35, (2 / 9)), (39, (1 / 1)), (52, (1 / 6)), (54, (-1 / 3)), (87, (1 / 2)), (123, (-1 / 3)), (226, (-1 / 6)), (228, (-1 / 6)), (237, (-1 / 6)), (306, (-1 / 6)), (315, (1 / 1)), (498, (1 / 2)), (507, (1 / 1)), (721, (-1 / 3)), (723, (-1 / 6)), (764, (1 / 1))]

def value3326 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-19 / 144)), (2, (1 / 48)), (3, (7 / 9)), (4, (2 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (12, (2 / 9)), (23, (-1 / 6)), (25, (-2 / 3)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 3)), (35, (2 / 9)), (51, (-2 / 3)), (52, (2 / 9)), (54, (-2 / 3)), (87, (1 / 2)), (89, (1 / 1)), (123, (-2 / 3)), (226, (-1 / 2)), (237, (-1 / 6))]

def value3327 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 36)), (2, (1 / 36)), (5, (-1 / 72)), (6, (1 / 288)), (17, (1 / 2)), (23, (-1 / 3)), (25, (-2 / 3)), (27, (1 / 24)), (31, (-1 / 2)), (63, (-1 / 6)), (87, (1 / 2)), (108, (1 / 2)), (123, (-1 / 3)), (124, (-1 / 6)), (196, (-1 / 6)), (203, (1 / 2)), (216, (1 / 2)), (226, (-1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3328 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 24)), (2, (7 / 96)), (5, (-1 / 24)), (6, (1 / 96)), (23, (-1 / 2)), (25, (-1 / 1)), (27, (1 / 8)), (31, (-1 / 1)), (68, (1 / 24)), (87, (3 / 2)), (123, (-1 / 1)), (124, (-1 / 2)), (196, (-1 / 3)), (226, (-1 / 2)), (237, (-1 / 2))]

def value3329 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (7 / 288)), (2, (5 / 288)), (23, (-1 / 6)), (25, (-1 / 3)), (27, (1 / 24)), (31, (-1 / 2)), (87, (1 / 2)), (108, (1 / 2)), (123, (-1 / 2)), (226, (-1 / 6)), (237, (-1 / 6))]

def value3330 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 12)), (2, (1 / 8)), (5, (-3 / 8)), (6, (1 / 24)), (7, (5 / 18)), (8, (5 / 9)), (9, (-1 / 9)), (69, (2 / 3)), (70, (2 / 9)), (71, (4 / 3))]

def value3331 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-13 / 288)), (2, (5 / 24)), (3, (1 / 1)), (4, (1 / 6)), (5, (-2 / 9)), (6, (1 / 72)), (7, (1 / 3)), (8, (1 / 3)), (12, (1 / 3)), (13, (13 / 18)), (35, (5 / 18)), (51, (-1 / 2)), (52, (1 / 2)), (59, (-1 / 2)), (60, (1 / 9)), (128, (1 / 6))]

def value3332 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 288)), (2, (1 / 24)), (3, (5 / 6)), (5, (-1 / 18)), (6, (1 / 288)), (7, (1 / 3)), (10, (-1 / 2)), (12, (1 / 3)), (13, (17 / 18)), (35, (11 / 18)), (52, (1 / 3)), (59, (-1 / 2)), (60, (1 / 9)), (82, (1 / 6)), (128, (1 / 6))]

def value3333 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (23 / 288)), (2, (-1 / 48)), (3, (1 / 6)), (5, (-7 / 72)), (6, (1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (5 / 18)), (35, (4 / 9)), (52, (1 / 3)), (60, (1 / 9))]

def value3334 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 18)), (2, (7 / 48)), (3, (2 / 9)), (5, (-13 / 36)), (6, (11 / 288)), (7, (7 / 18)), (8, (4 / 9)), (35, (2 / 9)), (52, (2 / 9))]

def value3335 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-1 / 72)), (2, (-17 / 288)), (3, (1 / 3)), (5, (1 / 24)), (6, (-1 / 72)), (7, (1 / 3)), (9, (-1 / 36)), (12, (1 / 9)), (13, (1 / 9)), (23, (-1 / 6)), (35, (2 / 9)), (69, (1 / 9)), (70, (1 / 9)), (124, (-1 / 6)), (196, (-1 / 6))]

def value3336 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-11 / 144)), (2, (7 / 288)), (3, (5 / 18)), (5, (-1 / 24)), (6, (1 / 96)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 6)), (26, (1 / 9)), (35, (1 / 9)), (54, (-1 / 6))]

def value3337 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-3 / 16)), (2, (1 / 24)), (3, (5 / 9)), (12, (1 / 6)), (13, (1 / 3))]

def value3338 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-11 / 144)), (2, (-1 / 96)), (3, (7 / 18)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 9)), (12, (1 / 9)), (13, (1 / 18)), (23, (-1 / 6)), (26, (1 / 9)), (35, (1 / 18)), (55, (-1 / 6))]

def value3339 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-11 / 96)), (2, (1 / 24)), (3, (4 / 9)), (4, (1 / 6)), (12, (1 / 9)), (26, (1 / 9))]

def value3340 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (5 / 48)), (2, (5 / 36)), (3, (1 / 6)), (5, (-7 / 24)), (6, (1 / 144)), (7, (2 / 3)), (8, (7 / 18)), (26, (1 / 18)), (35, (5 / 18)), (52, (1 / 18)), (59, (-1 / 6)), (67, (1 / 18)), (75, (1 / 2)), (81, (-1 / 6)), (428, (1 / 2))]

def value3341 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (1 / 8)), (2, (17 / 96)), (3, (4 / 9)), (5, (-23 / 72)), (6, (1 / 36)), (7, (1 / 3)), (8, (7 / 18)), (26, (1 / 9)), (33, (-1 / 6)), (35, (5 / 18)), (52, (1 / 3)), (67, (1 / 18)), (81, (-1 / 2)), (86, (1 / 2)), (428, (1 / 2)), (760, (1 / 2)), (855, (1 / 2))]

def value3342 : Sparse (Fin 909) := [(0, (-7 / 720)), (1, (1 / 8)), (2, (5 / 24)), (3, (11 / 18)), (4, (1 / 9)), (5, (-11 / 36)), (6, (1 / 48)), (7, (1 / 3)), (8, (7 / 18)), (11, (1 / 18)), (26, (1 / 6)), (35, (1 / 3)), (52, (4 / 9)), (81, (-5 / 6)), (86, (1 / 2)), (228, (-1 / 6)), (855, (1 / 2))]

def value3343 : Sparse (Fin 909) := [(0, (-1 / 90)), (1, (1 / 6)), (2, (5 / 24)), (3, (5 / 18)), (4, (1 / 18)), (5, (-23 / 72)), (6, (1 / 36)), (7, (1 / 6)), (8, (1 / 3)), (26, (1 / 9)), (35, (1 / 9)), (52, (7 / 18)), (81, (-1 / 6)), (85, (3 / 2)), (86, (1 / 2)), (228, (-1 / 3))]

def value3344 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 24)), (2, (-19 / 288)), (3, (2 / 9)), (5, (-1 / 8)), (6, (1 / 96)), (7, (7 / 18)), (8, (1 / 18)), (11, (2 / 9)), (26, (1 / 2)), (35, (8 / 9)), (67, (1 / 2)), (228, (-1 / 6)), (702, (1 / 2))]

def value3345 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-5 / 48)), (2, (1 / 9)), (3, (7 / 9)), (4, (1 / 6)), (5, (-13 / 72)), (6, (1 / 72)), (7, (11 / 18)), (8, (2 / 9)), (11, (1 / 18)), (26, (2 / 9)), (35, (4 / 9)), (52, (1 / 18)), (57, (1 / 1)), (86, (1 / 1)), (228, (-1 / 6)), (855, (2 / 1))]

def value3346 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 72)), (2, (1 / 144)), (3, (13 / 18)), (4, (1 / 6)), (5, (-5 / 24)), (6, (5 / 288)), (7, (5 / 9)), (8, (5 / 18)), (11, (1 / 6)), (26, (7 / 18)), (35, (2 / 3)), (52, (1 / 6)), (81, (-1 / 3)), (228, (-1 / 3)), (855, (1 / 2))]

def value3347 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-3 / 32)), (2, (35 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-19 / 72)), (6, (1 / 32)), (7, (7 / 18)), (8, (2 / 9)), (26, (1 / 3)), (35, (1 / 2)), (52, (1 / 3)), (67, (1 / 9)), (81, (-1 / 3))]

def value3348 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-5 / 288)), (2, (1 / 18)), (3, (7 / 9)), (4, (1 / 6)), (5, (-5 / 36)), (6, (1 / 72)), (7, (1 / 2)), (8, (1 / 9)), (11, (1 / 6)), (26, (4 / 9)), (35, (5 / 6)), (52, (5 / 18)), (67, (1 / 9)), (81, (-1 / 3)), (228, (-1 / 2))]

def value3349 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 96)), (2, (7 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (5 / 18)), (8, (1 / 9)), (26, (2 / 9)), (35, (7 / 18)), (52, (1 / 9)), (67, (1 / 9))]

def value3350 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-7 / 144)), (2, (11 / 144)), (3, (4 / 9)), (4, (1 / 9)), (5, (-13 / 72)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (11, (1 / 18)), (26, (1 / 6)), (35, (5 / 18)), (52, (1 / 6)), (81, (-1 / 6)), (228, (-1 / 6))]

def value3351 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-19 / 144)), (2, (7 / 144)), (3, (1 / 1)), (4, (1 / 2)), (5, (-1 / 18)), (6, (1 / 96)), (7, (1 / 6)), (11, (1 / 6)), (26, (2 / 3)), (35, (4 / 9)), (52, (1 / 6)), (228, (-1 / 2))]

def value3352 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-11 / 48)), (2, (35 / 288)), (3, (7 / 18)), (4, (1 / 3)), (5, (-1 / 36)), (8, (2 / 9)), (26, (1 / 9)), (30, (-1 / 3)), (31, (-1 / 3)), (40, (1 / 2)), (56, (-1 / 6)), (107, (1 / 1)), (239, (1 / 1))]

def value3353 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-5 / 36)), (2, (13 / 288)), (3, (5 / 9)), (4, (1 / 6)), (5, (-1 / 72)), (8, (1 / 18)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 9)), (40, (1 / 2)), (56, (-1 / 6))]

def value3354 : Sparse (Fin 909) := [(0, (17 / 720)), (1, (-43 / 144)), (2, (1 / 9)), (3, (7 / 9)), (4, (5 / 9)), (5, (-1 / 72)), (8, (1 / 18)), (26, (2 / 9)), (40, (1 / 2)), (56, (-1 / 6)), (57, (1 / 2))]

def value3355 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-17 / 96)), (2, (1 / 288)), (3, (11 / 18)), (4, (2 / 9)), (26, (5 / 18))]

def value3356 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-91 / 288)), (2, (19 / 144)), (3, (1 / 1)), (4, (4 / 9)), (26, (7 / 18)), (57, (1 / 2))]

def value3357 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-25 / 144)), (2, (13 / 96)), (3, (13 / 18)), (4, (1 / 3)), (5, (-1 / 72)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 3)), (31, (-1 / 3)), (33, (-2 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (177, (1 / 2))]

def value3358 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-41 / 288)), (2, (3 / 32)), (3, (1 / 1)), (4, (2 / 3)), (5, (-1 / 72)), (12, (1 / 6)), (13, (1 / 18)), (26, (1 / 3)), (52, (1 / 18)), (55, (-1 / 6)), (57, (1 / 1)), (119, (1 / 1)), (177, (1 / 2))]

def value3359 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-61 / 288)), (2, (1 / 16)), (3, (1 / 1)), (4, (11 / 18)), (26, (5 / 9)), (31, (-1 / 3)), (33, (-1 / 6)), (53, (1 / 2)), (57, (1 / 2)), (119, (1 / 1)), (204, (1 / 2))]

def value3360 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-19 / 144)), (2, (13 / 144)), (3, (2 / 3)), (4, (1 / 3)), (5, (-1 / 36)), (7, (1 / 18)), (8, (1 / 18)), (26, (5 / 18)), (31, (-1 / 3)), (33, (-5 / 6)), (37, (1 / 2)), (40, (1 / 2)), (51, (-1 / 6)), (55, (-1 / 2))]

def value3361 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 288)), (2, (1 / 36)), (3, (13 / 18)), (4, (1 / 18)), (5, (-5 / 72)), (6, (1 / 96)), (12, (1 / 18)), (13, (7 / 18)), (26, (1 / 3)), (34, (2 / 9)), (35, (2 / 9)), (51, (-1 / 6)), (52, (1 / 6)), (55, (-1 / 2)), (64, (-5 / 6)), (139, (1 / 2)), (238, (-1 / 3)), (546, (1 / 2))]

def value3362 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-29 / 288)), (2, (5 / 288)), (3, (23 / 18)), (4, (5 / 18)), (6, (1 / 288)), (12, (1 / 18)), (13, (1 / 6)), (26, (1 / 2)), (34, (1 / 2)), (35, (1 / 9)), (139, (1 / 2))]

def value3363 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 96)), (2, (1 / 36)), (3, (13 / 18)), (4, (5 / 18)), (5, (-1 / 12)), (6, (1 / 96)), (8, (1 / 9)), (13, (1 / 6)), (26, (4 / 9)), (34, (1 / 9)), (35, (5 / 18)), (52, (1 / 18)), (56, (-1 / 2)), (64, (-1 / 6)), (107, (1 / 2)), (190, (1 / 2)), (238, (-1 / 3)), (453, (1 / 1)), (870, (1 / 2))]

def value3364 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-11 / 288)), (2, (-1 / 72)), (3, (8 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (6, (1 / 144)), (13, (7 / 18)), (26, (1 / 2)), (34, (1 / 2)), (35, (2 / 9)), (52, (1 / 18)), (56, (-1 / 6)), (190, (1 / 2))]

def value3365 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-7 / 144)), (2, (31 / 288)), (3, (7 / 9)), (4, (7 / 18)), (5, (-1 / 8)), (6, (1 / 96)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 3)), (31, (-1 / 6)), (35, (1 / 9)), (45, (1 / 2)), (51, (-1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (107, (3 / 2)), (238, (-1 / 3)), (870, (1 / 2))]

def value3366 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (1 / 72)), (2, (1 / 144)), (3, (2 / 3)), (4, (1 / 6)), (5, (-13 / 72)), (6, (7 / 288)), (8, (1 / 18)), (9, (-1 / 72)), (11, (1 / 9)), (13, (1 / 2)), (26, (1 / 3)), (35, (11 / 18)), (52, (7 / 18)), (56, (-1 / 3)), (69, (1 / 18)), (71, (1 / 18)), (262, (-1 / 3)), (796, (-1 / 6)), (870, (1 / 2))]

def value3367 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (1 / 32)), (2, (-1 / 288)), (3, (11 / 18)), (4, (1 / 6)), (5, (-1 / 6)), (6, (5 / 288)), (8, (1 / 9)), (11, (1 / 6)), (13, (4 / 9)), (26, (4 / 9)), (35, (11 / 18)), (52, (1 / 6)), (56, (-1 / 3)), (228, (-1 / 6)), (546, (1 / 2)), (870, (1 / 2))]

def value3368 : Sparse (Fin 909) := [(0, (7 / 1440)), (1, (-3 / 16)), (2, (1 / 96)), (3, (23 / 18)), (4, (5 / 9)), (5, (-1 / 36)), (6, (1 / 144)), (12, (2 / 9)), (13, (2 / 9)), (26, (5 / 9)), (35, (1 / 6)), (52, (1 / 18)), (56, (-1 / 3)), (204, (1 / 2))]

def value3369 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-1 / 36)), (2, (7 / 72)), (3, (7 / 9)), (4, (2 / 9)), (5, (-1 / 18)), (6, (1 / 144)), (12, (1 / 6)), (13, (1 / 6)), (26, (2 / 9)), (27, (1 / 24)), (31, (-1 / 3)), (35, (1 / 18)), (43, (1 / 2)), (51, (-2 / 3)), (52, (1 / 6)), (204, (1 / 2)), (237, (-1 / 6)), (238, (-1 / 6)), (546, (1 / 2)), (745, (1 / 1))]

def value3370 : Sparse (Fin 909) := [(0, (31 / 1440)), (1, (-103 / 288)), (2, (7 / 72)), (3, (7 / 6)), (4, (4 / 9)), (12, (7 / 18)), (13, (7 / 18)), (26, (2 / 9)), (31, (-1 / 3)), (33, (-1 / 3)), (34, (1 / 9))]

def value3371 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-7 / 48)), (2, (5 / 144)), (3, (11 / 9)), (4, (1 / 3)), (12, (4 / 9)), (13, (1 / 2)), (26, (4 / 9)), (33, (-1 / 3)), (34, (1 / 9)), (35, (1 / 6)), (55, (-1 / 2))]

def value3372 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-3 / 32)), (2, (1 / 48)), (3, (11 / 18)), (4, (2 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 3)), (34, (1 / 9))]

def value3373 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-47 / 288)), (2, (5 / 144)), (3, (5 / 9)), (4, (1 / 6)), (26, (2 / 9))]

def value3374 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-5 / 24)), (2, (7 / 288)), (3, (5 / 18)), (4, (2 / 9)), (26, (1 / 9))]

def value3375 : Sparse (Fin 909) := [(0, (19 / 720)), (1, (-29 / 96)), (2, (1 / 96)), (3, (1 / 1)), (4, (2 / 3)), (12, (1 / 3)), (13, (1 / 9)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value3376 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (1 / 8)), (2, (7 / 48)), (3, (1 / 6)), (5, (-5 / 18)), (6, (1 / 36)), (7, (11 / 18)), (8, (7 / 18)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 3)), (52, (1 / 9)), (59, (-2 / 3)), (71, (1 / 6)), (82, (1 / 18)), (199, (-1 / 6)), (201, (-1 / 6)), (289, (1 / 2)), (309, (-1 / 6))]

def value3377 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (29 / 288)), (2, (1 / 8)), (3, (2 / 9)), (5, (-2 / 9)), (6, (7 / 288)), (7, (7 / 18)), (8, (4 / 9)), (13, (1 / 9)), (35, (2 / 9)), (52, (2 / 9)), (56, (-1 / 6)), (59, (-5 / 6)), (76, (1 / 2)), (201, (-1 / 2)), (506, (1 / 2))]

def value3378 : Sparse (Fin 909) := [(0, (-11 / 1440)), (1, (43 / 288)), (2, (2 / 9)), (3, (5 / 9)), (5, (-7 / 18)), (6, (1 / 24)), (7, (2 / 9)), (8, (7 / 18)), (12, (1 / 18)), (13, (2 / 9)), (35, (4 / 9)), (51, (-1 / 6)), (52, (13 / 18)), (71, (1 / 9)), (82, (1 / 18)), (86, (1 / 2)), (128, (1 / 18)), (201, (-1 / 6)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (328, (1 / 2))]

def value3379 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 288)), (2, (23 / 144)), (3, (7 / 18)), (5, (-13 / 72)), (6, (1 / 72)), (7, (1 / 18)), (8, (1 / 3)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 18)), (45, (1 / 2)), (51, (-1 / 3)), (52, (5 / 18)), (71, (1 / 9)), (102, (1 / 1)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2)), (739, (1 / 2)), (870, (1 / 2))]

def value3380 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 24)), (2, (23 / 144)), (3, (5 / 9)), (4, (1 / 9)), (5, (-2 / 9)), (6, (7 / 288)), (7, (1 / 18)), (8, (2 / 9)), (12, (1 / 18)), (13, (1 / 6)), (26, (1 / 18)), (35, (2 / 9)), (45, (1 / 2)), (51, (-1 / 3)), (52, (1 / 2)), (56, (-1 / 6)), (102, (1 / 1)), (103, (1 / 2)), (739, (1 / 2)), (870, (1 / 2))]

def value3381 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (31 / 288)), (2, (17 / 96)), (3, (7 / 18)), (5, (-23 / 72)), (6, (5 / 144)), (7, (2 / 9)), (8, (1 / 6)), (35, (7 / 18)), (42, (1 / 2)), (52, (2 / 3)), (86, (1 / 2)), (328, (1 / 1)), (506, (1 / 2)), (798, (1 / 2))]

def value3382 : Sparse (Fin 909) := [(0, (-7 / 1440)), (1, (-1 / 288)), (2, (-1 / 144)), (3, (1 / 3)), (5, (-1 / 8)), (6, (1 / 48)), (7, (5 / 18)), (8, (1 / 9)), (13, (2 / 9)), (26, (1 / 6)), (35, (1 / 3)), (52, (1 / 6)), (54, (-2 / 3)), (69, (1 / 18)), (70, (1 / 18)), (71, (1 / 18)), (103, (1 / 2)), (228, (-1 / 3)), (286, (1 / 2)), (309, (-1 / 6)), (739, (1 / 2))]

def value3383 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 96)), (3, (1 / 2)), (5, (-7 / 72)), (6, (7 / 288)), (7, (2 / 9)), (8, (1 / 18)), (13, (2 / 9)), (26, (1 / 6)), (35, (1 / 6)), (51, (-1 / 6)), (52, (1 / 6)), (54, (-2 / 3)), (55, (-1 / 6)), (77, (1 / 2)), (228, (-1 / 2)), (737, (1 / 2)), (739, (1 / 2))]

def value3384 : Sparse (Fin 909) := [(0, (-13 / 1440)), (1, (13 / 288)), (2, (43 / 288)), (3, (8 / 9)), (5, (-13 / 72)), (6, (7 / 288)), (7, (1 / 6)), (8, (1 / 18)), (12, (2 / 9)), (13, (13 / 18)), (35, (7 / 18)), (51, (-1 / 3)), (52, (11 / 18)), (69, (1 / 18)), (70, (1 / 18)), (102, (1 / 2)), (262, (-1 / 6)), (309, (-1 / 6)), (327, (1 / 2))]

def value3385 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (5 / 48)), (3, (5 / 6)), (4, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 18)), (8, (1 / 18)), (12, (2 / 9)), (13, (2 / 3)), (26, (1 / 18)), (35, (5 / 18)), (51, (-1 / 3)), (52, (4 / 9)), (56, (-1 / 6)), (102, (1 / 2)), (103, (1 / 2))]

def value3386 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (7 / 288)), (2, (1 / 12)), (3, (4 / 9)), (4, (1 / 18)), (5, (-1 / 8)), (6, (5 / 288)), (12, (1 / 6)), (13, (1 / 2)), (26, (1 / 18)), (35, (2 / 9)), (43, (1 / 2)), (52, (4 / 9)), (102, (1 / 2)), (103, (1 / 1)), (546, (1 / 2)), (737, (1 / 2))]

def value3387 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (5 / 48)), (3, (11 / 18)), (5, (-5 / 24)), (6, (1 / 32)), (7, (2 / 9)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 2)), (35, (4 / 9)), (52, (5 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (82, (1 / 18)), (128, (1 / 6)), (201, (-1 / 6))]

def value3388 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 144)), (2, (5 / 72)), (3, (5 / 18)), (5, (-1 / 9)), (6, (1 / 96)), (7, (1 / 9)), (8, (1 / 6)), (12, (1 / 9)), (13, (1 / 9)), (35, (1 / 18)), (51, (-1 / 6)), (52, (1 / 9))]

def value3389 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (5 / 144)), (2, (5 / 48)), (3, (4 / 9)), (5, (-19 / 72)), (6, (5 / 144)), (7, (5 / 18)), (8, (1 / 6)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 2)), (52, (1 / 2)), (59, (-1 / 6)), (60, (1 / 9)), (128, (1 / 18))]

def value3390 : Sparse (Fin 909) := [(0, (1 / 60)), (1, (-7 / 72)), (2, (1 / 24)), (3, (2 / 3)), (4, (2 / 9)), (12, (5 / 18)), (13, (2 / 9))]

def value3391 : Sparse (Fin 909) := [(0, (13 / 1440)), (1, (-25 / 144)), (2, (11 / 288)), (3, (5 / 9)), (4, (1 / 6)), (12, (1 / 3)), (13, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3392 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (5 / 288)), (2, (-1 / 32)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 9)), (6, (1 / 72)), (7, (1 / 6)), (8, (1 / 9)), (26, (1 / 9)), (35, (1 / 18)), (51, (-1 / 6)), (52, (1 / 18))]

def value3393 : Sparse (Fin 909) := [(0, (41 / 1440)), (1, (-1 / 6)), (2, (1 / 32)), (3, (5 / 18)), (4, (1 / 3)), (12, (1 / 6))]

def value3394 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 48)), (3, (1 / 9)), (5, (-5 / 18)), (6, (11 / 288)), (7, (1 / 18)), (8, (2 / 9)), (35, (1 / 9)), (52, (1 / 3))]

def value3395 : Sparse (Fin 909) := [(0, (1 / 180)), (1, (-17 / 144)), (2, (-5 / 288)), (3, (1 / 3)), (5, (-1 / 36)), (6, (1 / 288)), (12, (1 / 18)), (13, (5 / 18)), (35, (1 / 18)), (52, (1 / 9))]

def value3396 : Sparse (Fin 909) := [(0, (29 / 1440)), (1, (-3 / 16)), (2, (13 / 96)), (3, (2 / 3)), (4, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (51, (-1 / 2)), (52, (1 / 6))]

def value3397 : Sparse (Fin 909) := [(0, (-53 / 720)), (1, (-13 / 72)), (2, (1 / 144)), (3, (1 / 9)), (4, (2 / 9)), (12, (1 / 18))]

def value3398 : Sparse (Fin 909) := [(0, (-1 / 40)), (1, (-7 / 72)), (2, (1 / 18)), (17, (1 / 2)), (28, (1 / 1)), (30, (-1 / 2))]

def value3399 : Sparse (Fin 909) := [(0, (-19 / 240)), (1, (-5 / 16)), (2, (1 / 12)), (27, (1 / 24)), (28, (1 / 2)), (30, (-1 / 3))]

def value3400 : Sparse (Fin 909) := [(0, (1 / 480)), (1, (-7 / 288)), (2, (17 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-5 / 72)), (6, (1 / 288)), (7, (1 / 18)), (8, (1 / 9)), (26, (1 / 9)), (35, (1 / 18)), (52, (1 / 9))]

def value3401 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (-1 / 96)), (2, (35 / 288)), (3, (11 / 18)), (4, (1 / 9)), (5, (-2 / 9)), (6, (1 / 72)), (7, (11 / 18)), (8, (1 / 3)), (26, (2 / 9)), (35, (1 / 2)), (52, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value3402 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-25 / 96)), (2, (1 / 24)), (3, (10 / 9)), (4, (4 / 9)), (12, (2 / 9)), (13, (5 / 18)), (26, (7 / 18)), (33, (-1 / 6)), (34, (1 / 9))]

def value3403 : Sparse (Fin 909) := [(0, (1 / 160)), (1, (-29 / 144)), (2, (5 / 96)), (3, (5 / 18)), (4, (2 / 9)), (26, (1 / 18)), (31, (-1 / 6))]

def value3404 : Sparse (Fin 909) := [(0, (-67 / 1440)), (1, (-17 / 72)), (2, (1 / 32)), (3, (1 / 18)), (4, (1 / 9)), (12, (1 / 18))]

def value3405 : Sparse (Fin 909) := [(0, (19 / 1440)), (1, (-11 / 288)), (2, (1 / 24)), (3, (7 / 18)), (4, (2 / 9)), (12, (1 / 6)), (13, (1 / 18))]

def value3406 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (1 / 18)), (2, (59 / 288)), (3, (1 / 6)), (5, (-25 / 72)), (6, (1 / 48)), (7, (1 / 2)), (8, (2 / 3)), (35, (1 / 9))]

def value3407 : Sparse (Fin 909) := [(0, (7 / 480)), (1, (-3 / 16)), (2, (7 / 288)), (3, (7 / 18)), (4, (1 / 9)), (26, (1 / 9))]

def value3408 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (7 / 288)), (3, (5 / 18)), (5, (-1 / 8)), (6, (1 / 144)), (11, (1 / 18)), (13, (13 / 18)), (26, (1 / 9)), (35, (1 / 2)), (52, (1 / 2)), (56, (-1 / 6)), (60, (1 / 2)), (82, (1 / 18)), (128, (1 / 9)), (324, (1 / 2))]

def value3409 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (-19 / 288)), (2, (1 / 96)), (3, (1 / 1)), (4, (1 / 6)), (5, (-1 / 36)), (6, (1 / 144)), (12, (1 / 9)), (13, (2 / 9)), (26, (1 / 2)), (34, (1 / 6)), (35, (5 / 18)), (55, (-1 / 3)), (139, (1 / 2)), (204, (1 / 1)), (238, (-1 / 3)), (398, (1 / 1))]

def value3410 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 18)), (2, (1 / 16)), (5, (5 / 36)), (6, (5 / 144)), (7, (1 / 9)), (8, (-1 / 18)), (35, (1 / 9)), (52, (1 / 9)), (56, (-1 / 3)), (71, (1 / 9)), (74, (1 / 2)), (201, (-1 / 3)), (507, (1 / 1))]

def value3411 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (31 / 288)), (2, (1 / 8)), (3, (1 / 18)), (5, (-23 / 72)), (6, (5 / 144)), (8, (1 / 3)), (35, (1 / 18)), (39, (1 / 2)), (52, (1 / 3)), (71, (1 / 9)), (315, (1 / 1)), (507, (1 / 2)), (764, (1 / 2))]

def value3412 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (7 / 96)), (2, (35 / 288)), (3, (4 / 9)), (5, (-17 / 72)), (6, (5 / 144)), (7, (5 / 18)), (8, (1 / 9)), (12, (1 / 18)), (13, (7 / 18)), (35, (11 / 18)), (52, (5 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (82, (2 / 9)), (128, (5 / 18)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3413 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 18)), (3, (5 / 9)), (5, (-7 / 72)), (6, (1 / 48)), (7, (1 / 18)), (12, (5 / 18)), (13, (5 / 6)), (35, (5 / 18)), (52, (2 / 9)), (54, (-1 / 6)), (82, (2 / 9)), (128, (2 / 9)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3414 : Sparse (Fin 909) := [(1, (-5 / 288)), (2, (29 / 288)), (3, (5 / 6)), (4, (2 / 9)), (5, (-5 / 18)), (6, (7 / 144)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 6)), (13, (11 / 18)), (26, (2 / 9)), (35, (1 / 2)), (52, (4 / 9)), (54, (-1 / 6)), (56, (-1 / 3)), (82, (2 / 9)), (128, (2 / 9)), (199, (-1 / 6)), (201, (-1 / 3))]

def value3415 : Sparse (Fin 909) := [(1, (-17 / 144)), (2, (1 / 48)), (3, (10 / 9)), (4, (4 / 9)), (12, (1 / 9)), (13, (1 / 3)), (26, (11 / 18)), (33, (-1 / 6)), (34, (1 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3416 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-37 / 288)), (2, (1 / 144)), (3, (1 / 2)), (4, (1 / 9)), (12, (5 / 18)), (13, (5 / 18)), (26, (1 / 9)), (34, (1 / 9))]

def value3417 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-65 / 288)), (2, (-5 / 288)), (3, (5 / 6)), (4, (4 / 9)), (12, (1 / 3)), (13, (5 / 18)), (25, (-1 / 6)), (26, (2 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3418 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-1 / 16)), (2, (7 / 144)), (3, (1 / 2)), (4, (1 / 9)), (5, (-5 / 36)), (6, (1 / 72)), (8, (1 / 9)), (12, (1 / 18)), (25, (-1 / 6)), (26, (1 / 9)), (35, (1 / 9)), (51, (-1 / 3)), (52, (1 / 3)), (54, (-1 / 6)), (89, (1 / 2)), (123, (-1 / 3)), (226, (-1 / 6))]

def value3419 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-41 / 288)), (2, (1 / 48)), (3, (1 / 2)), (4, (1 / 9)), (12, (1 / 18)), (13, (1 / 9)), (26, (1 / 9)), (33, (-1 / 6))]

def value3420 : Sparse (Fin 909) := [(1, (-1 / 288)), (2, (5 / 288)), (3, (1 / 6)), (5, (-11 / 72)), (6, (1 / 48)), (7, (1 / 6)), (8, (1 / 9)), (11, (1 / 18)), (26, (1 / 18)), (35, (5 / 18)), (52, (2 / 9)), (228, (-1 / 6))]

def value3421 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 288)), (2, (5 / 144)), (3, (5 / 18)), (5, (-5 / 36)), (6, (1 / 72)), (7, (1 / 3)), (8, (2 / 9)), (9, (-1 / 36)), (35, (2 / 9)), (69, (5 / 18)), (70, (1 / 6)), (71, (1 / 9))]

def value3422 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 288)), (2, (5 / 144)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 6)), (52, (1 / 9))]

def value3423 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-1 / 16)), (2, (13 / 144)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (2 / 9)), (8, (1 / 18)), (12, (1 / 9)), (13, (1 / 9)), (26, (1 / 9)), (35, (1 / 6)), (51, (-1 / 6)), (52, (1 / 6))]

def value3424 : Sparse (Fin 909) := [(0, (-1 / 720)), (1, (1 / 36)), (2, (1 / 36)), (3, (1 / 9)), (5, (-1 / 12)), (6, (1 / 144)), (7, (1 / 9)), (8, (1 / 9)), (12, (1 / 18)), (13, (2 / 9)), (35, (1 / 6)), (52, (1 / 9)), (59, (-1 / 6)), (60, (1 / 9)), (128, (1 / 18))]

def value3425 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-11 / 96)), (2, (1 / 32)), (3, (7 / 9)), (4, (1 / 9)), (12, (1 / 3)), (13, (7 / 18))]

def value3426 : Sparse (Fin 909) := [(0, (1 / 72)), (1, (-13 / 48)), (2, (7 / 144)), (3, (8 / 9)), (4, (2 / 9)), (12, (5 / 9)), (13, (1 / 3))]

def value3427 : Sparse (Fin 909) := [(0, (-1 / 288)), (1, (-5 / 288)), (2, (1 / 144)), (3, (5 / 18)), (12, (2 / 9)), (13, (11 / 18)), (32, (1 / 9))]

def value3428 : Sparse (Fin 909) := [(1, (13 / 288)), (2, (1 / 48)), (3, (1 / 9)), (4, (1 / 9)), (5, (-1 / 18)), (6, (1 / 288)), (8, (1 / 9)), (26, (2 / 9)), (35, (1 / 6)), (52, (1 / 9)), (67, (1 / 9)), (81, (-1 / 3))]

def value3429 : Sparse (Fin 909) := [(0, (37 / 1440)), (1, (-7 / 32)), (2, (5 / 144)), (3, (5 / 9)), (4, (7 / 18)), (12, (1 / 18)), (26, (1 / 6)), (31, (-1 / 6))]

def value3430 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 96)), (2, (7 / 288)), (3, (7 / 18)), (4, (1 / 9)), (12, (1 / 18)), (13, (1 / 18)), (26, (1 / 6)), (33, (-1 / 6)), (34, (1 / 9))]

def value3431 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-5 / 288)), (2, (5 / 288)), (3, (5 / 9)), (4, (2 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (26, (1 / 3)), (34, (1 / 9)), (35, (1 / 9))]

def value3432 : Sparse (Fin 909) := [(0, (7 / 360)), (1, (-13 / 72)), (2, (1 / 36)), (3, (2 / 3)), (4, (1 / 3)), (12, (1 / 9)), (26, (2 / 9))]

def value3433 : Sparse (Fin 909) := [(0, (23 / 1440)), (1, (-19 / 72)), (2, (11 / 288)), (3, (1 / 6)), (4, (1 / 3)), (12, (1 / 18))]

def value3434 : Sparse (Fin 909) := [(0, (-7 / 480)), (1, (-5 / 144)), (2, (1 / 32)), (3, (1 / 18))]

def value3435 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (1 / 288)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 9)), (13, (1 / 6)), (26, (1 / 9)), (33, (-1 / 3)), (34, (1 / 9))]

def value3436 : Sparse (Fin 909) := [(0, (13 / 720)), (1, (-11 / 72)), (2, (7 / 144)), (3, (1 / 3)), (4, (2 / 9)), (12, (2 / 9))]

def value3437 : Sparse (Fin 909) := [(0, (-11 / 480)), (1, (1 / 12)), (2, (7 / 288)), (3, (1 / 6)), (4, (1 / 9))]

def value3438 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-1 / 32)), (2, (11 / 288)), (3, (4 / 9)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (12, (1 / 9)), (13, (5 / 18)), (26, (2 / 9)), (34, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value3439 : Sparse (Fin 909) := [(1, (-1 / 72)), (2, (5 / 96)), (3, (1 / 6)), (5, (-7 / 72)), (6, (1 / 96)), (7, (2 / 9)), (8, (1 / 9)), (35, (1 / 9))]

def value3440 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-5 / 48)), (2, (1 / 48)), (3, (2 / 9)), (12, (1 / 6)), (13, (1 / 9))]

def value3441 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 16)), (2, (-1 / 32)), (3, (1 / 6)), (4, (1 / 9)), (26, (1 / 9))]

def value3442 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 144)), (2, (1 / 144)), (3, (1 / 9)), (4, (1 / 9)), (12, (1 / 18))]

def value3443 : Sparse (Fin 909) := [(0, (1 / 720)), (1, (-13 / 288)), (2, (-1 / 144)), (3, (2 / 9)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 18)), (12, (1 / 9)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 9)), (54, (-1 / 6))]

def value3444 : Sparse (Fin 909) := [(0, (11 / 1440)), (1, (-5 / 48)), (2, (17 / 288)), (3, (1 / 2)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (5 / 18)), (23, (-1 / 6)), (24, (-1 / 6))]

def value3445 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-1 / 9)), (2, (1 / 36)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 9)), (8, (1 / 18)), (12, (1 / 9)), (23, (-1 / 6)), (24, (-1 / 6))]

def value3446 : Sparse (Fin 909) := [(0, (-1 / 1440)), (1, (-23 / 144)), (2, (1 / 32)), (3, (1 / 6)), (4, (2 / 9)), (12, (1 / 9))]

def value3447 : Sparse (Fin 909) := [(0, (1 / 144)), (1, (-13 / 144)), (2, (1 / 72)), (3, (1 / 3)), (4, (1 / 9)), (5, (-1 / 72)), (7, (1 / 6)), (26, (1 / 9)), (35, (1 / 9))]

def value3448 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-19 / 96)), (2, (1 / 288)), (3, (7 / 9)), (4, (1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (26, (1 / 3)), (35, (1 / 6)), (55, (-1 / 2))]

def value3449 : Sparse (Fin 909) := [(0, (1 / 1440)), (1, (-1 / 72)), (2, (19 / 288)), (3, (1 / 2)), (4, (1 / 6)), (5, (-5 / 24)), (6, (5 / 144)), (7, (1 / 6)), (8, (1 / 9)), (11, (1 / 6)), (26, (1 / 3)), (35, (4 / 9)), (52, (5 / 18)), (228, (-1 / 2))]

def value3450 : Sparse (Fin 909) := [(0, (11 / 360)), (1, (-1 / 36)), (2, (1 / 72))]

def value3451 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-3 / 16)), (2, (-1 / 16)), (3, (11 / 18)), (4, (2 / 9)), (12, (1 / 9)), (13, (1 / 3)), (26, (2 / 9)), (35, (1 / 6)), (54, (-1 / 6)), (56, (-1 / 3))]

def value3452 : Sparse (Fin 909) := [(0, (7 / 720)), (1, (-7 / 72)), (2, (11 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (6, (1 / 288)), (7, (1 / 9)), (26, (1 / 9)), (35, (1 / 9)), (52, (1 / 9))]

def value3453 : Sparse (Fin 909) := [(0, (1 / 360)), (1, (-5 / 72)), (2, (5 / 72)), (3, (2 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9))]

def value3454 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (1 / 144)), (2, (1 / 144)), (3, (7 / 18)), (5, (-7 / 72)), (6, (1 / 72)), (7, (1 / 3)), (8, (1 / 9)), (9, (-1 / 72)), (26, (1 / 9)), (35, (1 / 2)), (52, (1 / 9)), (67, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3455 : Sparse (Fin 909) := [(0, (17 / 1440)), (1, (-19 / 144)), (2, (23 / 288)), (3, (7 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (26, (1 / 9))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value3456 : Sparse (Fin 909) := [(1, (1 / 288)), (2, (13 / 288)), (3, (1 / 9)), (5, (-1 / 9)), (6, (1 / 72)), (7, (2 / 9)), (9, (-1 / 72)), (35, (1 / 9)), (52, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3457 : Sparse (Fin 909) := [(0, (-1 / 180)), (1, (1 / 72)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9))]

def value3458 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-1 / 18)), (2, (19 / 288)), (3, (5 / 18)), (4, (1 / 9)), (5, (-1 / 24)), (7, (1 / 18)), (8, (1 / 9)), (12, (1 / 9))]

def value3459 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (11 / 144)), (3, (1 / 6)), (5, (-5 / 36)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3)), (9, (-1 / 72)), (35, (1 / 9)), (69, (1 / 6)), (70, (1 / 9))]

def value3460 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-7 / 288)), (2, (1 / 8)), (3, (4 / 9)), (4, (1 / 9)), (5, (-5 / 24)), (6, (5 / 288)), (7, (5 / 18)), (8, (1 / 3)), (9, (-1 / 72)), (26, (1 / 9)), (35, (1 / 6)), (52, (1 / 9)), (69, (1 / 9)), (70, (1 / 18)), (71, (1 / 9))]

def value3461 : Sparse (Fin 909) := [(0, (1 / 90)), (1, (-17 / 144)), (2, (-1 / 72)), (5, (-1 / 12)), (6, (1 / 48)), (25, (-1 / 3)), (31, (-2 / 3)), (87, (1 / 2)), (123, (-2 / 3)), (226, (-1 / 6)), (237, (-1 / 2)), (239, (1 / 1))]

def value3462 : Sparse (Fin 909) := [(0, (-1 / 96)), (1, (13 / 288)), (2, (1 / 96)), (5, (-1 / 36)), (6, (1 / 288)), (27, (1 / 8)), (28, (1 / 1)), (30, (-2 / 3)), (31, (-1 / 6)), (203, (1 / 2)), (236, (-1 / 6)), (253, (2 / 1))]

def value3463 : Sparse (Fin 909) := [(0, (1 / 80)), (1, (7 / 144)), (2, (1 / 48)), (5, (-1 / 18)), (6, (1 / 144)), (17, (1 / 2)), (23, (-1 / 6)), (25, (-1 / 6)), (27, (1 / 8)), (30, (-1 / 6)), (203, (1 / 1)), (216, (1 / 2)), (236, (-1 / 6)), (253, (1 / 1))]

def value3464 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 12)), (3, (1 / 3)), (4, (1 / 18)), (5, (-1 / 4)), (6, (11 / 288)), (7, (1 / 18)), (8, (1 / 9)), (11, (1 / 18)), (26, (1 / 9)), (35, (1 / 3)), (52, (1 / 2)), (228, (-1 / 6))]

def value3465 : Sparse (Fin 909) := [(0, (-1 / 360)), (1, (-5 / 72)), (2, (5 / 288)), (3, (17 / 18)), (4, (2 / 9)), (5, (-1 / 36)), (6, (1 / 288)), (7, (1 / 18)), (12, (1 / 3)), (13, (7 / 9)), (26, (2 / 9)), (35, (1 / 3)), (52, (1 / 9)), (54, (-1 / 3)), (56, (-1 / 3))]

def value3466 : Sparse (Fin 909) := [(0, (1 / 120)), (1, (-13 / 144)), (2, (53 / 288)), (3, (1 / 2)), (5, (-13 / 72)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 3)), (12, (1 / 6)), (13, (1 / 9)), (35, (1 / 9))]

def value3467 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-59 / 288)), (2, (11 / 288)), (3, (4 / 3)), (4, (2 / 3)), (5, (-1 / 72)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 9)), (26, (2 / 3)), (35, (5 / 18)), (55, (-1 / 2))]

def value3468 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (7 / 72)), (3, (5 / 6)), (4, (1 / 6)), (5, (-13 / 72)), (6, (1 / 48)), (7, (1 / 2)), (9, (-1 / 72)), (11, (1 / 6)), (26, (1 / 3)), (35, (7 / 9)), (52, (1 / 2)), (69, (1 / 6)), (70, (1 / 9)), (228, (-1 / 2))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value384 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (1 / 32)), (5, (-1 / 8)), (7, (1 / 2)), (9, (-1 / 24)), (69, (1 / 2)), (70, (1 / 3))]

def value385 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 3)), (35, (1 / 3)), (69, (1 / 6)), (70, (1 / 3)), (277, (-1 / 2)), (278, (1 / 6))]

def value386 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-5 / 24)), (6, (5 / 96)), (9, (-1 / 6)), (58, (1 / 96)), (69, (1 / 6)), (71, (1 / 3))]

def value387 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 96)), (8, (1 / 3)), (9, (-1 / 24)), (69, (1 / 6)), (71, (2 / 3))]

def value388 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 6)), (9, (-1 / 12)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 2))]

def value389 : Sparse (Fin 909) := [(2, (1 / 48)), (5, (-1 / 8)), (6, (1 / 48)), (7, (1 / 6)), (9, (-1 / 24)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 3))]

def value390 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 48)), (5, (-1 / 24)), (6, (1 / 48)), (9, (-1 / 8)), (35, (1 / 6)), (58, (1 / 96)), (70, (1 / 3)), (71, (1 / 6)), (278, (1 / 6))]

def value391 : Sparse (Fin 909) := [(279, (1 / 1))]

def value392 : Sparse (Fin 909) := [(280, (1 / 1))]

def value393 : Sparse (Fin 909) := [(281, (1 / 1))]

def value394 : Sparse (Fin 909) := [(282, (1 / 1))]

def value395 : Sparse (Fin 909) := [(72, (1 / 1))]

def value396 : Sparse (Fin 909) := [(73, (1 / 1))]

def value397 : Sparse (Fin 909) := [(74, (1 / 1))]

def value398 : Sparse (Fin 909) := [(75, (1 / 1))]

def value399 : Sparse (Fin 909) := [(284, (1 / 1))]

def value400 : Sparse (Fin 909) := [(286, (1 / 1))]

def value401 : Sparse (Fin 909) := [(287, (1 / 1))]

def value402 : Sparse (Fin 909) := [(288, (1 / 1))]

def value403 : Sparse (Fin 909) := [(289, (1 / 1))]

def value404 : Sparse (Fin 909) := [(76, (1 / 1))]

def value405 : Sparse (Fin 909) := [(290, (1 / 1))]

def value406 : Sparse (Fin 909) := [(291, (1 / 1))]

def value407 : Sparse (Fin 909) := [(293, (1 / 1))]

def value408 : Sparse (Fin 909) := [(77, (1 / 1))]

def value409 : Sparse (Fin 909) := [(78, (1 / 1))]

def value410 : Sparse (Fin 909) := [(299, (1 / 1))]

def value411 : Sparse (Fin 909) := [(300, (1 / 1))]

def value412 : Sparse (Fin 909) := [(79, (1 / 1))]

def value413 : Sparse (Fin 909) := [(80, (1 / 1))]

def value414 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (6, (1 / 24)), (9, (-1 / 6))]

def value415 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (69, (1 / 6)), (495, (1 / 6))]

def value416 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 8)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (69, (1 / 3)), (70, (1 / 6)), (71, (1 / 6))]

def value417 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6)), (81, (-1 / 2)), (256, (-1 / 2))]

def value418 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (1 / 16)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3)), (69, (1 / 6)), (71, (1 / 2))]

def value419 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 16)), (2, (5 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (8, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (81, (-1 / 2))]

def value420 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (35, (1 / 3)), (67, (1 / 6))]

def value421 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (5, (-1 / 24)), (7, (1 / 3)), (26, (1 / 6)), (35, (1 / 2)), (52, (1 / 6)), (67, (1 / 6))]

def value422 : Sparse (Fin 909) := [(3, (1 / 3)), (4, (1 / 6)), (7, (1 / 6)), (26, (1 / 3)), (35, (1 / 3)), (67, (1 / 6)), (81, (-1 / 2))]

def value423 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 6)), (35, (1 / 6)), (81, (-1 / 2)), (228, (-1 / 2)), (273, (-1 / 2))]

def value424 : Sparse (Fin 909) := [(10, (-1 / 2)), (55, (-1 / 2)), (273, (-1 / 2)), (306, (-1 / 2))]

def value425 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (1 / 12)), (5, (-1 / 6)), (6, (1 / 32)), (35, (1 / 6)), (52, (1 / 3)), (306, (-1 / 2))]

def value426 : Sparse (Fin 909) := [(3, (1 / 6)), (7, (1 / 6)), (11, (1 / 6)), (26, (1 / 3)), (34, (1 / 6)), (35, (1 / 2)), (67, (1 / 3)), (276, (1 / 6))]

def value427 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 3)), (67, (1 / 6)), (307, (-1 / 2))]

def value428 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (-1 / 96)), (11, (1 / 3)), (35, (1 / 2)), (82, (1 / 6)), (276, (1 / 3))]

def value429 : Sparse (Fin 909) := [(1, (-7 / 96)), (2, (-1 / 32)), (5, (1 / 8)), (7, (1 / 6)), (9, (-1 / 24)), (69, (1 / 6))]

def value430 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (5, (-1 / 24)), (35, (1 / 6)), (69, (1 / 6)), (70, (1 / 6))]

def value431 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 24)), (5, (-1 / 24)), (6, (1 / 48)), (9, (-1 / 12)), (52, (1 / 6)), (58, (1 / 96)), (310, (1 / 6))]

def value432 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (5 / 96)), (5, (-1 / 24)), (6, (1 / 48)), (8, (1 / 6)), (9, (-1 / 24)), (71, (1 / 6))]

def value433 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 16)), (2, (1 / 24)), (5, (-1 / 12)), (71, (1 / 3))]

def value434 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 16)), (5, (-1 / 6)), (7, (1 / 3)), (8, (1 / 3)), (69, (1 / 6)), (71, (1 / 6))]

def value435 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 8)), (6, (1 / 24)), (7, (1 / 6)), (9, (-1 / 24)), (35, (1 / 3)), (70, (1 / 6))]

def value436 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (-1 / 8)), (6, (-1 / 48)), (9, (-1 / 24)), (35, (1 / 6)), (58, (1 / 96)), (82, (1 / 3)), (278, (1 / 6)), (310, (1 / 6))]

def value437 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 12)), (2, (1 / 32)), (3, (1 / 2)), (5, (-1 / 24)), (7, (1 / 2)), (35, (1 / 3))]

def value438 : Sparse (Fin 909) := [(3, (1 / 3)), (7, (1 / 6)), (10, (-1 / 2)), (12, (1 / 6)), (13, (1 / 3)), (35, (1 / 3)), (82, (1 / 6))]

def value439 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (7 / 96)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 48)), (52, (1 / 3)), (308, (-1 / 2)), (310, (1 / 6))]

def value440 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 12)), (2, (5 / 48)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (8, (1 / 3))]

def value441 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 12)), (5, (-1 / 8)), (7, (1 / 6)), (8, (1 / 3))]

def value442 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 6)), (51, (-1 / 2)), (308, (-1 / 2)), (309, (-1 / 2))]

def value443 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 96)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 8)), (6, (1 / 96)), (7, (1 / 3)), (8, (1 / 6)), (35, (1 / 6))]

def value444 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (309, (-1 / 2)), (310, (1 / 6))]

def value445 : Sparse (Fin 909) := [(1, (5 / 96)), (2, (-1 / 32)), (5, (-1 / 8)), (13, (1 / 6)), (35, (1 / 3)), (82, (1 / 6))]

def value446 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (7, (1 / 3)), (8, (1 / 3)), (10, (-1 / 2))]

def value447 : Sparse (Fin 909) := [(311, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value448 : Sparse (Fin 909) := [(312, (1 / 1))]

def value449 : Sparse (Fin 909) := [(83, (1 / 1))]

def value450 : Sparse (Fin 909) := [(84, (1 / 1))]

def value451 : Sparse (Fin 909) := [(313, (1 / 1))]

def value452 : Sparse (Fin 909) := [(314, (1 / 1))]

def value453 : Sparse (Fin 909) := [(315, (1 / 1))]

def value454 : Sparse (Fin 909) := [(85, (1 / 1))]

def value455 : Sparse (Fin 909) := [(316, (1 / 1))]

def value456 : Sparse (Fin 909) := [(317, (1 / 1))]

def value457 : Sparse (Fin 909) := [(318, (1 / 1))]

def value458 : Sparse (Fin 909) := [(319, (1 / 1))]

def value459 : Sparse (Fin 909) := [(321, (1 / 1))]

def value460 : Sparse (Fin 909) := [(322, (1 / 1))]

def value461 : Sparse (Fin 909) := [(323, (1 / 1))]

def value462 : Sparse (Fin 909) := [(324, (1 / 1))]

def value463 : Sparse (Fin 909) := [(325, (1 / 1))]

def value464 : Sparse (Fin 909) := [(86, (1 / 1))]

def value465 : Sparse (Fin 909) := [(326, (1 / 1))]

def value466 : Sparse (Fin 909) := [(327, (1 / 1))]

def value467 : Sparse (Fin 909) := [(328, (1 / 1))]

def value468 : Sparse (Fin 909) := [(329, (1 / 1))]

def value469 : Sparse (Fin 909) := [(330, (1 / 1))]

def value470 : Sparse (Fin 909) := [(352, (1 / 1))]

def value471 : Sparse (Fin 909) := [(87, (1 / 1))]

def value472 : Sparse (Fin 909) := [(36, (1 / 1))]

def value473 : Sparse (Fin 909) := [(37, (1 / 1))]

def value474 : Sparse (Fin 909) := [(38, (1 / 1))]

def value475 : Sparse (Fin 909) := [(89, (1 / 1))]

def value476 : Sparse (Fin 909) := [(39, (1 / 1))]

def value477 : Sparse (Fin 909) := [(40, (1 / 1))]

def value478 : Sparse (Fin 909) := [(378, (1 / 1))]

def value479 : Sparse (Fin 909) := [(379, (1 / 1))]

def value480 : Sparse (Fin 909) := [(383, (1 / 1))]

def value481 : Sparse (Fin 909) := [(41, (1 / 1))]

def value482 : Sparse (Fin 909) := [(94, (1 / 1))]

def value483 : Sparse (Fin 909) := [(95, (1 / 1))]

def value484 : Sparse (Fin 909) := [(97, (1 / 1))]

def value485 : Sparse (Fin 909) := [(98, (1 / 1))]

def value486 : Sparse (Fin 909) := [(392, (1 / 1))]

def value487 : Sparse (Fin 909) := [(99, (1 / 1))]

def value488 : Sparse (Fin 909) := [(100, (1 / 1))]

def value489 : Sparse (Fin 909) := [(101, (1 / 1))]

def value490 : Sparse (Fin 909) := [(42, (1 / 1))]

def value491 : Sparse (Fin 909) := [(102, (1 / 1))]

def value492 : Sparse (Fin 909) := [(398, (1 / 1))]

def value493 : Sparse (Fin 909) := [(399, (1 / 1))]

def value494 : Sparse (Fin 909) := [(400, (1 / 1))]

def value495 : Sparse (Fin 909) := [(103, (1 / 1))]

def value496 : Sparse (Fin 909) := [(104, (1 / 1))]

def value497 : Sparse (Fin 909) := [(105, (1 / 1))]

def value498 : Sparse (Fin 909) := [(425, (1 / 1))]

def value499 : Sparse (Fin 909) := [(426, (1 / 1))]

def value500 : Sparse (Fin 909) := [(106, (1 / 1))]

def value501 : Sparse (Fin 909) := [(428, (1 / 1))]

def value502 : Sparse (Fin 909) := [(107, (1 / 1))]

def value503 : Sparse (Fin 909) := [(108, (1 / 1))]

def value504 : Sparse (Fin 909) := [(110, (1 / 1))]

def value505 : Sparse (Fin 909) := [(112, (1 / 1))]

def value506 : Sparse (Fin 909) := [(113, (1 / 1))]

def value507 : Sparse (Fin 909) := [(114, (1 / 1))]

def value508 : Sparse (Fin 909) := [(115, (1 / 1))]

def value509 : Sparse (Fin 909) := [(453, (1 / 1))]

def value510 : Sparse (Fin 909) := [(43, (1 / 1))]

def value511 : Sparse (Fin 909) := [(116, (1 / 1))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value512 : Sparse (Fin 909) := [(460, (1 / 1))]

def value513 : Sparse (Fin 909) := [(44, (1 / 1))]

def value514 : Sparse (Fin 909) := [(45, (1 / 1))]

def value515 : Sparse (Fin 909) := [(119, (1 / 1))]

def value516 : Sparse (Fin 909) := [(120, (1 / 1))]

def value517 : Sparse (Fin 909) := [(46, (1 / 1))]

def value518 : Sparse (Fin 909) := [(122, (1 / 1))]

def value519 : Sparse (Fin 909) := [(472, (1 / 1))]

def value520 : Sparse (Fin 909) := [(47, (1 / 1))]

def value521 : Sparse (Fin 909) := [(48, (1 / 1))]

def value522 : Sparse (Fin 909) := [(49, (1 / 1))]

def value523 : Sparse (Fin 909) := [(50, (1 / 1))]

def value524 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6)), (126, (-1 / 2)), (262, (-1 / 2))]

def value525 : Sparse (Fin 909) := [(124, (-1 / 2)), (126, (-1 / 2)), (197, (-1 / 2)), (236, (-1 / 2))]

def value526 : Sparse (Fin 909) := [(486, (1 / 1))]

def value527 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (1 / 24)), (3, (1 / 3)), (12, (1 / 6)), (13, (2 / 3)), (52, (1 / 3)), (128, (1 / 6))]

def value528 : Sparse (Fin 909) := [(51, (-1 / 2)), (123, (-1 / 2)), (124, (-1 / 2)), (259, (-1 / 2))]

def value529 : Sparse (Fin 909) := [(3, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (33, (-1 / 2)), (51, (-1 / 2)), (59, (-1 / 2))]

def value530 : Sparse (Fin 909) := [(125, (-1 / 1)), (126, (-1 / 1))]

def value531 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (1 / 12)), (3, (1 / 3)), (5, (-1 / 24)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 3))]

def value532 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (26, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (123, (-1 / 2))]

def value533 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (51, (-1 / 2)), (54, (-1 / 2)), (64, (-1 / 2))]

def value534 : Sparse (Fin 909) := [(487, (1 / 1))]

def value535 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 24)), (2, (1 / 32)), (3, (1 / 3)), (4, (1 / 6)), (26, (1 / 6)), (33, (-1 / 2)), (81, (-1 / 2))]

def value536 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (25, (-1 / 2)), (26, (1 / 6)), (64, (-1 / 2)), (123, (-1 / 2))]

def value537 : Sparse (Fin 909) := [(33, (-1 / 1)), (489, (-1 / 1))]

def value538 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 6)), (52, (1 / 6)), (123, (-1 / 2)), (237, (-1 / 2)), (489, (-1 / 2))]

def value539 : Sparse (Fin 909) := [(31, (-1 / 2)), (33, (-1 / 2)), (51, (-1 / 2)), (123, (-1 / 2))]

def value540 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 24)), (5, (-1 / 12)), (6, (1 / 96)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 3)), (60, (1 / 6)), (128, (1 / 6)), (490, (-1 / 2))]

def value541 : Sparse (Fin 909) := [(1, (-1 / 12)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 3)), (69, (1 / 6)), (124, (-1 / 2))]

def value542 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 6)), (7, (1 / 6)), (23, (-1 / 2)), (124, (-1 / 2)), (125, (-1 / 2))]

def value543 : Sparse (Fin 909) := [(1, (1 / 24)), (2, (5 / 96)), (5, (-1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (9, (-1 / 24)), (35, (1 / 6)), (52, (1 / 3)), (69, (1 / 3)), (495, (1 / 6))]

def value544 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (1 / 32)), (2, (1 / 16)), (3, (1 / 6)), (5, (-1 / 12)), (7, (1 / 6)), (52, (1 / 6)), (69, (1 / 6)), (126, (-1 / 2))]

def value545 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (1 / 24)), (2, (1 / 48)), (8, (1 / 6)), (24, (-1 / 2)), (126, (-1 / 1))]

def value546 : Sparse (Fin 909) := [(27, (1 / 8)), (68, (1 / 8)), (124, (-1 / 2)), (126, (-1 / 2)), (493, (-1 / 2))]

def value547 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 48)), (2, (1 / 96)), (27, (1 / 8)), (51, (-1 / 2)), (124, (-1 / 2)), (126, (-1 / 2))]

def value548 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 24)), (68, (1 / 8)), (125, (-1 / 2)), (126, (-1 / 2)), (494, (-1 / 2))]

def value549 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (13, (1 / 6)), (52, (1 / 3)), (69, (1 / 6)), (125, (-1 / 2))]

def value550 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 32)), (6, (1 / 48)), (9, (-1 / 24)), (52, (1 / 6)), (69, (1 / 6)), (128, (1 / 6)), (492, (-1 / 2)), (495, (1 / 6))]

def value551 : Sparse (Fin 909) := [(1, (-1 / 32)), (2, (1 / 96)), (3, (1 / 3)), (7, (1 / 3)), (13, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (125, (-1 / 2))]

def value552 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (5, (-1 / 8)), (6, (1 / 32)), (9, (-1 / 12)), (52, (1 / 3)), (58, (1 / 96)), (69, (1 / 6)), (310, (1 / 3)), (495, (1 / 3))]

def value553 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (3 / 32)), (2, (11 / 96)), (5, (-5 / 24)), (6, (1 / 32)), (9, (-1 / 24)), (52, (1 / 3)), (69, (1 / 6))]

def value554 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (5 / 48)), (2, (7 / 96)), (5, (-1 / 12)), (8, (1 / 3)), (71, (1 / 6)), (126, (-1 / 2))]

def value555 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 48)), (2, (-1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6))]

def value556 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 16)), (2, (1 / 96)), (7, (1 / 6)), (12, (1 / 6)), (13, (1 / 6)), (35, (1 / 6))]

def value558 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (35, (1 / 6)), (310, (1 / 6)), (495, (1 / 6))]

def value559 : Sparse (Fin 909) := [(0, (-1 / 240)), (2, (1 / 32)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (52, (1 / 6))]

def value560 : Sparse (Fin 909) := [(0, (1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (5, (-1 / 24)), (8, (1 / 6))]

def value561 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (1 / 96)), (2, (1 / 16)), (3, (1 / 6)), (5, (-1 / 24)), (7, (1 / 6)), (8, (1 / 6)), (51, (-1 / 2))]

def value562 : Sparse (Fin 909) := [(1, (-1 / 24)), (2, (1 / 12)), (3, (1 / 3)), (5, (-1 / 24)), (7, (1 / 6))]

def value563 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (5 / 96)), (2, (1 / 96)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 6))]

def value564 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (5 / 96)), (5, (-1 / 8)), (6, (1 / 32)), (13, (1 / 6)), (52, (1 / 3)), (82, (1 / 6)), (128, (1 / 3)), (310, (1 / 6)), (495, (1 / 6))]

def value565 : Sparse (Fin 909) := [(1, (1 / 32)), (2, (1 / 32)), (5, (-1 / 8)), (13, (1 / 6)), (52, (1 / 3)), (82, (1 / 6)), (128, (1 / 3))]

def value566 : Sparse (Fin 909) := [(0, (-1 / 160)), (1, (-1 / 8)), (2, (1 / 96)), (3, (1 / 2)), (12, (1 / 2)), (13, (1 / 3))]

def value567 : Sparse (Fin 909) := [(3, (1 / 3)), (12, (1 / 3)), (13, (2 / 3)), (127, (-1 / 2)), (128, (1 / 6))]

def value568 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (3, (1 / 3)), (26, (1 / 6)), (35, (1 / 3)), (52, (1 / 3)), (493, (-1 / 2)), (495, (1 / 6))]

def value569 : Sparse (Fin 909) := [(0, (-1 / 160)), (2, (5 / 96)), (3, (1 / 3)), (4, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6))]

def value570 : Sparse (Fin 909) := [(0, (1 / 96)), (1, (-1 / 16)), (2, (7 / 96)), (3, (1 / 6))]

def value571 : Sparse (Fin 909) := [(51, (-1 / 2)), (55, (-1 / 2)), (493, (-1 / 2)), (494, (-1 / 2))]

def value572 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 48)), (2, (1 / 24)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6)), (51, (-1 / 2)), (52, (1 / 6))]

def value573 : Sparse (Fin 909) := [(0, (-1 / 120)), (1, (-5 / 96)), (2, (1 / 32)), (3, (1 / 3)), (12, (1 / 6)), (13, (1 / 6))]

def value574 : Sparse (Fin 909) := [(1, (1 / 32)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 3)), (35, (1 / 6)), (52, (1 / 6)), (128, (1 / 6)), (494, (-1 / 2)), (495, (1 / 6))]

def value575 : Sparse (Fin 909) := [(1, (7 / 96)), (2, (1 / 24)), (3, (1 / 6)), (5, (-1 / 24)), (6, (1 / 96)), (13, (1 / 2)), (52, (1 / 3)), (128, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Values9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def value576 : Sparse (Fin 909) := [(498, (1 / 1))]

def value577 : Sparse (Fin 909) := [(499, (1 / 1))]

def value578 : Sparse (Fin 909) := [(500, (1 / 1))]

def value579 : Sparse (Fin 909) := [(501, (1 / 1))]

def value580 : Sparse (Fin 909) := [(502, (1 / 1))]

def value581 : Sparse (Fin 909) := [(503, (1 / 1))]

def value582 : Sparse (Fin 909) := [(505, (1 / 1))]

def value583 : Sparse (Fin 909) := [(506, (1 / 1))]

def value584 : Sparse (Fin 909) := [(507, (1 / 1))]

def value585 : Sparse (Fin 909) := [(508, (1 / 1))]

def value586 : Sparse (Fin 909) := [(517, (1 / 1))]

def value587 : Sparse (Fin 909) := [(129, (1 / 1))]

def value588 : Sparse (Fin 909) := [(137, (1 / 1))]

def value589 : Sparse (Fin 909) := [(138, (1 / 1))]

def value590 : Sparse (Fin 909) := [(139, (1 / 1))]

def value591 : Sparse (Fin 909) := [(140, (1 / 1))]

def value592 : Sparse (Fin 909) := [(141, (1 / 1))]

def value593 : Sparse (Fin 909) := [(538, (1 / 1))]

def value594 : Sparse (Fin 909) := [(539, (1 / 1))]

def value595 : Sparse (Fin 909) := [(540, (1 / 1))]

def value596 : Sparse (Fin 909) := [(541, (1 / 1))]

def value597 : Sparse (Fin 909) := [(543, (1 / 1))]

def value598 : Sparse (Fin 909) := [(142, (1 / 1))]

def value599 : Sparse (Fin 909) := [(143, (1 / 1))]

def value600 : Sparse (Fin 909) := [(545, (1 / 1))]

def value601 : Sparse (Fin 909) := [(144, (1 / 1))]

def value602 : Sparse (Fin 909) := [(145, (1 / 1))]

def value603 : Sparse (Fin 909) := [(146, (1 / 1))]

def value604 : Sparse (Fin 909) := [(546, (1 / 1))]

def value605 : Sparse (Fin 909) := [(14, (1 / 1))]

def value606 : Sparse (Fin 909) := [(15, (1 / 1))]

def value607 : Sparse (Fin 909) := [(16, (1 / 1))]

def value608 : Sparse (Fin 909) := [(17, (1 / 1))]

def value609 : Sparse (Fin 909) := [(18, (1 / 1))]

def value610 : Sparse (Fin 909) := [(640, (1 / 1))]

def value611 : Sparse (Fin 909) := [(643, (1 / 1))]

def value612 : Sparse (Fin 909) := [(177, (1 / 1))]

def value613 : Sparse (Fin 909) := [(19, (1 / 1))]

def value614 : Sparse (Fin 909) := [(20, (1 / 1))]

def value615 : Sparse (Fin 909) := [(702, (1 / 1))]

def value616 : Sparse (Fin 909) := [(190, (1 / 1))]

def value617 : Sparse (Fin 909) := [(191, (1 / 1))]

def value618 : Sparse (Fin 909) := [(709, (1 / 1))]

def value619 : Sparse (Fin 909) := [(53, (1 / 1))]

def value620 : Sparse (Fin 909) := [(21, (1 / 1))]

def value621 : Sparse (Fin 909) := [(22, (1 / 1))]

def value622 : Sparse (Fin 909) := [(194, (1 / 1))]

def value623 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 96)), (5, (-1 / 24)), (7, (1 / 6)), (35, (1 / 6)), (59, (-1 / 2)), (199, (-1 / 2)), (271, (-1 / 2))]

def value624 : Sparse (Fin 909) := [(0, (-1 / 240)), (1, (-1 / 16)), (3, (1 / 3)), (12, (1 / 3)), (33, (-1 / 1))]

def value625 : Sparse (Fin 909) := [(195, (1 / 1))]

def value626 : Sparse (Fin 909) := [(0, (-1 / 480)), (1, (-1 / 32)), (3, (1 / 6)), (4, (1 / 6)), (25, (-1 / 2)), (31, (-1 / 2)), (33, (-1 / 2))]

def value627 : Sparse (Fin 909) := [(55, (-1 / 2)), (63, (-1 / 2)), (237, (-1 / 2)), (306, (-1 / 2))]

def value628 : Sparse (Fin 909) := [(54, (-1 / 2)), (228, (-1 / 2)), (271, (-1 / 2)), (721, (-1 / 2))]

def value629 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 96)), (5, (-1 / 12)), (6, (1 / 32)), (13, (1 / 6)), (35, (1 / 6)), (52, (1 / 6)), (82, (1 / 6)), (128, (1 / 6)), (721, (-1 / 2))]

def value630 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 48)), (5, (-1 / 12)), (8, (1 / 6)), (59, (-1 / 1)), (201, (-1 / 2))]

def value631 : Sparse (Fin 909) := [(23, (-1 / 2)), (54, (-1 / 2)), (125, (-1 / 2)), (196, (-1 / 2))]

def value632 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (-1 / 24)), (5, (-1 / 24)), (6, (1 / 32)), (7, (1 / 6)), (9, (-1 / 24)), (11, (1 / 6)), (35, (1 / 2)), (70, (1 / 3)), (278, (1 / 6))]

def value633 : Sparse (Fin 909) := [(1, (-1 / 48)), (2, (-5 / 96)), (3, (1 / 6)), (6, (1 / 96)), (7, (1 / 6)), (26, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (197, (-1 / 2))]

def value634 : Sparse (Fin 909) := [(24, (-1 / 2)), (56, (-1 / 2)), (197, (-1 / 1))]

def value635 : Sparse (Fin 909) := [(1, (-1 / 96)), (2, (-1 / 96)), (5, (-1 / 24)), (55, (-1 / 2)), (125, (-1 / 2)), (197, (-1 / 2))]

def value636 : Sparse (Fin 909) := [(1, (1 / 48)), (2, (1 / 24)), (6, (1 / 48)), (13, (1 / 6)), (35, (1 / 3)), (70, (1 / 6)), (196, (-1 / 2))]

def value637 : Sparse (Fin 909) := [(2, (-1 / 24)), (5, (-1 / 24)), (6, (-1 / 24)), (9, (-1 / 24)), (35, (1 / 6)), (70, (1 / 6)), (82, (1 / 6)), (278, (1 / 6)), (723, (-1 / 2))]

def value638 : Sparse (Fin 909) := [(1, (1 / 96)), (2, (1 / 48)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 6)), (9, (-1 / 12)), (35, (1 / 6)), (69, (1 / 6)), (70, (1 / 6)), (278, (1 / 6)), (495, (1 / 6)), (726, (-1 / 2))]

def value639 : Sparse (Fin 909) := [(1, (-1 / 96)), (3, (1 / 6)), (5, (-1 / 12)), (6, (1 / 96)), (7, (1 / 3)), (35, (1 / 3)), (52, (1 / 6)), (69, (1 / 6)), (70, (1 / 6))]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue0 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (27, (-5 / 12)), (68, (-5 / 6))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue1 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue10 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue11 : Sparse (Fin 909) := [(0, (-11 / 1296)), (2, (5 / 1296)), (5, (5 / 1296)), (8, (5 / 162)), (20, (-5 / 36)), (24, (-5 / 108)), (27, (-5 / 432)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue12 : Sparse (Fin 909) := [(0, (67 / 2592)), (1, (-65 / 2592)), (2, (-5 / 432)), (3, (5 / 81)), (4, (5 / 81)), (5, (5 / 1296)), (8, (5 / 162)), (12, (5 / 162)), (17, (-5 / 36)), (24, (-5 / 54)), (27, (-5 / 432)), (30, (5 / 108)), (68, (-5 / 216)), (126, (-5 / 27)), (203, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue13 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue14 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue15 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue16 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue17 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue18 : Sparse (Fin 909) := [(0, (223 / 5184)), (1, (-205 / 5184)), (2, (65 / 2592)), (3, (5 / 162)), (4, (5 / 162)), (68, (-5 / 216)), (126, (-5 / 54)), (203, (-5 / 36)), (236, (-5 / 54)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue19 : Sparse (Fin 909) := [(0, (5 / 648)), (1, (-5 / 432)), (2, (5 / 1296)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue2 : Sparse (Fin 909) := [(0, (5 / 216)), (1, (5 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (24, (-5 / 18)), (27, (-5 / 72)), (68, (-5 / 36)), (126, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue20 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue21 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue22 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue23 : Sparse (Fin 909) := [(0, (5 / 648)), (1, (-5 / 432)), (2, (5 / 1296)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue24 : Sparse (Fin 909) := [(0, (223 / 5184)), (1, (-205 / 5184)), (2, (65 / 2592)), (3, (5 / 162)), (4, (5 / 162)), (68, (-5 / 216)), (126, (-5 / 54)), (203, (-5 / 36)), (236, (-5 / 54)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue25 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-185 / 1296)), (2, (5 / 192)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (-5 / 1296)), (7, (-10 / 81)), (12, (-10 / 81)), (23, (-5 / 27)), (27, (-5 / 108)), (58, (5 / 5184)), (68, (5 / 216)), (69, (-5 / 81)), (230, (5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue26 : Sparse (Fin 909) := [(0, (-1 / 2592)), (1, (-10 / 81)), (2, (5 / 432)), (5, (-5 / 648)), (6, (5 / 864)), (7, (-5 / 27)), (12, (-5 / 27)), (13, (-10 / 81)), (23, (-5 / 18)), (27, (5 / 216)), (35, (-10 / 81)), (63, (-5 / 27))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue3 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue4 : Sparse (Fin 909) := [(0, (17 / 432)), (1, (-5 / 144)), (2, (5 / 216)), (68, (-5 / 36)), (126, (-5 / 18)), (236, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue5 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue6 : Sparse (Fin 909) := [(0, (2 / 81)), (1, (25 / 648)), (2, (-5 / 648)), (5, (5 / 1296)), (8, (5 / 162)), (27, (-5 / 432)), (28, (-5 / 36)), (30, (-5 / 108)), (68, (-5 / 216)), (236, (-5 / 27)), (253, (-5 / 18))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue7 : Sparse (Fin 909) := [(0, (-11 / 1296)), (2, (5 / 1296)), (5, (5 / 1296)), (8, (5 / 162)), (20, (-5 / 36)), (24, (-5 / 108)), (27, (-5 / 432)), (68, (-5 / 216)), (126, (-5 / 54)), (208, (-5 / 18)), (236, (-5 / 54))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue8 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairTargets_Partition9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue9 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

end MUB6.Certificate.PairTargetSemantics

end OAI
end


