-- Prove2me | Definitions.Def_OAIQ106E071
-- name    : OAIQ106E071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:21:41.390364+00:00
-- url     : https://prove2.me/theorems/befc41b7-43ce-4004-b6a7-241523c51bdd
-- title:
--   Definitions bundle OAIQ106E071 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7664 declarations of OpenAI's Lean: 7664 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedData.row918`, `OAI.MUB6.Certificate.MixedData.row920`, `OAI.MUB6.Certificate.MixedData.row921`, `OAI.MUB6.Certificate.MixedData.row922`, `OAI.MUB6.Certificate.MixedData.row923`, `OAI.MUB6.Certificate.MixedData.row924`, `OAI.MUB6.Certificate.MixedData.row925`, `OAI.MUB6.Certificate.MixedData.row926`, `OAI.MUB6.Certificate.MixedData.row927`, `OAI.MUB6.Certificate.MixedData.row928`, `OAI.MUB6.Certificate.MixedData.row929`, `OAI.MUB6.Certificate.MixedData.row930`, `OAI.MUB6.Certificate.MixedData.row931`, `OAI.MUB6.Certificate.MixedData.row932`, `OAI.MUB6.Certificate.MixedData.row933`, `OAI.MUB6.Certificate.MixedData.row934`, `OAI.MUB6.Certificate.MixedData.row935`, `OAI.MUB6.Certificate.MixedData.row936`, `OAI.MUB6.Certificate.MixedData.row937`, `OAI.MUB6.Certificate.MixedData.row938`, `OAI.MUB6.Certificate.MixedData.row939`, `OAI.MUB6.Certificate.MixedData.row940`, `OAI.MUB6.Certificate.MixedData.row941`, `OAI.MUB6.Certificate.MixedData.row942`, `OAI.MUB6.Certificate.MixedData.row943`, `OAI.MUB6.Certificate.MixedData.row944`, `OAI.MUB6.Certificate.MixedData.row945`, `OAI.MUB6.Certificate.MixedData.row946`, `OAI.MUB6.Certificate.MixedData.row947`, `OAI.MUB6.Certificate.MixedData.row948`, `OAI.MUB6.Certificate.MixedData.row949`, `OAI.MUB6.Certificate.MixedData.row950`, `OAI.MUB6.Certificate.MixedData.row951`, `OAI.MUB6.Certificate.MixedData.row952`, `OAI.MUB6.Certificate.MixedData.row953`, `OAI.MUB6.Certificate.MixedData.row954`, `OAI.MUB6.Certificate.MixedData.row955`, `OAI.MUB6.Certificate.MixedData.row956`, `OAI.MUB6.Certificate.MixedData.row957`, `OAI.MUB6.Certificate.MixedData.row958` and 7624 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedData_Source0`, `MutuallyUnbiased_MixedData_Source7`, `MutuallyUnbiased_MixedData_Targets`, `MutuallyUnbiased_MixedSemantics_PairAverage`, `MutuallyUnbiased_MixedSemantics_Sources0`, `MutuallyUnbiased_MixedSemantics_Sources1`, `MutuallyUnbiased_MixedSemantics_Sources10`, `MutuallyUnbiased_MixedSemantics_Sources11`, `MutuallyUnbiased_MixedSemantics_Sources12`, `MutuallyUnbiased_MixedSemantics_Sources13`, `MutuallyUnbiased_MixedSemantics_Sources14`, `MutuallyUnbiased_MixedSemantics_Sources15`, `MutuallyUnbiased_MixedSemantics_Sources16`, `MutuallyUnbiased_MixedSemantics_Sources17`, `MutuallyUnbiased_MixedSemantics_Sources18`, `MutuallyUnbiased_MixedSemantics_Sources19`, `MutuallyUnbiased_MixedSemantics_Sources2`, `MutuallyUnbiased_MixedSemantics_Sources20`, `MutuallyUnbiased_MixedSemantics_Sources21`, `MutuallyUnbiased_MixedSemantics_Sources22`, `MutuallyUnbiased_MixedSemantics_Sources23`, `MutuallyUnbiased_MixedSemantics_Sources24`, `MutuallyUnbiased_MixedSemantics_Sources25`, `MutuallyUnbiased_MixedSemantics_Sources26`, `MutuallyUnbiased_MixedSemantics_Sources27`, `MutuallyUnbiased_MixedSemantics_Sources28`, `MutuallyUnbiased_MixedSemantics_Sources29`, `MutuallyUnbiased_MixedSemantics_Sources3`, `MutuallyUnbiased_MixedSemantics_Sources30`, `MutuallyUnbiased_MixedSemantics_Sources31`, `MutuallyUnbiased_MixedSemantics_Sources32`, `MutuallyUnbiased_MixedSemantics_Sources33`, `MutuallyUnbiased_MixedSemantics_Sources34`, `MutuallyUnbiased_MixedSemantics_Sources35`, `MutuallyUnbiased_MixedSemantics_Sources36`, `MutuallyUnbiased_MixedSemantics_Sources37`, `MutuallyUnbiased_MixedSemantics_Sources38`, `MutuallyUnbiased_MixedSemantics_Sources39`, `MutuallyUnbiased_MixedSemantics_Sources4`, `MutuallyUnbiased_MixedSemantics_Sources40`, `MutuallyUnbiased_MixedSemantics_Sources41`, `MutuallyUnbiased_MixedSemantics_Sources42`, `MutuallyUnbiased_MixedSemantics_Sources43`, `MutuallyUnbiased_MixedSemantics_Sources44`, `MutuallyUnbiased_MixedSemantics_Sources45`, `MutuallyUnbiased_MixedSemantics_Sources46`, `MutuallyUnbiased_MixedSemantics_Sources47`, `MutuallyUnbiased_MixedSemantics_Sources48`, `MutuallyUnbiased_MixedSemantics_Sources49`, `MutuallyUnbiased_MixedSemantics_Sources5`, `MutuallyUnbiased_MixedSemantics_Sources50`, `MutuallyUnbiased_MixedSemantics_Sources51`, `MutuallyUnbiased_MixedSemantics_Sources52`, `MutuallyUnbiased_MixedSemantics_Sources53`, `MutuallyUnbiased_MixedSemantics_Sources54`, `MutuallyUnbiased_MixedSemantics_Sources55`, `MutuallyUnbiased_MixedSemantics_Sources56`, `MutuallyUnbiased_MixedSemantics_Sources57`, `MutuallyUnbiased_MixedSemantics_Sources58`, `MutuallyUnbiased_MixedSemantics_Sources59`, `MutuallyUnbiased_MixedSemantics_Sources6`, `MutuallyUnbiased_MixedSemantics_Sources60`, `MutuallyUnbiased_MixedSemantics_Sources61`, `MutuallyUnbiased_MixedSemantics_Sources62`, `MutuallyUnbiased_MixedSemantics_Sources63`, `MutuallyUnbiased_MixedSemantics_Sources64`, `MutuallyUnbiased_MixedSemantics_Sources65`, `MutuallyUnbiased_MixedSemantics_Sources66`, `MutuallyUnbiased_MixedSemantics_Sources67`, `MutuallyUnbiased_MixedSemantics_Sources68`, `MutuallyUnbiased_MixedSemantics_Sources69`, `MutuallyUnbiased_MixedSemantics_Sources7`, `MutuallyUnbiased_MixedSemantics_Sources70`, `MutuallyUnbiased_MixedSemantics_Sources71`, `MutuallyUnbiased_MixedSemantics_Sources72`, `MutuallyUnbiased_MixedSemantics_Sources73`, `MutuallyUnbiased_MixedSemantics_Sources74`, `MutuallyUnbiased_MixedSemantics_Sources75`, `MutuallyUnbiased_MixedSemantics_Sources76`, `MutuallyUnbiased_MixedSemantics_Sources77`, `MutuallyUnbiased_MixedSemantics_Sources78`, `MutuallyUnbiased_MixedSemantics_Sources79`, `MutuallyUnbiased_MixedSemantics_Sources8`, `MutuallyUnbiased_MixedSemantics_Sources80`, `MutuallyUnbiased_MixedSemantics_Sources81`, `MutuallyUnbiased_MixedSemantics_Sources82`, `MutuallyUnbiased_MixedSemantics_Sources83`, `MutuallyUnbiased_MixedSemantics_Sources84`, `MutuallyUnbiased_MixedSemantics_Sources85`, `MutuallyUnbiased_MixedSemantics_Sources86`, `MutuallyUnbiased_MixedSemantics_Sources9`, `MutuallyUnbiased_Moments_OrderedPairs`, `MutuallyUnbiased_PairMerge_Block0`, `MutuallyUnbiased_PairMerge_Block3`, `MutuallyUnbiased_PairMerge_Block4`, `MutuallyUnbiased_PairMerge_Block5`, `MutuallyUnbiased_PairMerge_Block6`, `MutuallyUnbiased_PairSemantics_Coordinates`, `MutuallyUnbiased_PairSemantics_Coordinates0`, `MutuallyUnbiased_PairSemantics_Coordinates1`, `MutuallyUnbiased_PairSemantics_Coordinates10`, `MutuallyUnbiased_PairSemantics_Coordinates11`, `MutuallyUnbiased_PairSemantics_Coordinates12`, `MutuallyUnbiased_PairSemantics_Coordinates13`, `MutuallyUnbiased_PairSemantics_Coordinates14`, `MutuallyUnbiased_PairSemantics_Coordinates2`, `MutuallyUnbiased_PairSemantics_Coordinates3`, `MutuallyUnbiased_PairSemantics_Coordinates4`, `MutuallyUnbiased_PairSemantics_Coordinates5`, `MutuallyUnbiased_PairSemantics_Coordinates6`, `MutuallyUnbiased_PairSemantics_Coordinates7`, `MutuallyUnbiased_PairSemantics_Coordinates8`, `MutuallyUnbiased_PairSemantics_Coordinates9`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundle `OAIQ106E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E072`, `OAIQ106E076`, `OAIQ106E078`, `OAIQ106E086`, `OAIQ106E133`, `OAIQ106E149` and `OAIQ106E171`; the statements `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`; the proofs of `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e` and `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E000

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row96 : Integer.Sparse (Fin 3237) := [(1631, 3), (1632, 1), (2580, 1), (2833, -1)]

def row97 : Integer.Sparse (Fin 3237) := [(0, 13), (32, -5), (160, 80), (225, 160), (261, 130), (503, -2160), (507, -720), (518, -2160), (520, -1440), (521, -720), (780, -2160), (869, -720), (1316, -4320), (1329, -4320), (1331, -4320), (1332, -2160), (1473, -2160), (1620, -4320), (1622, -720), (1628, -2160), (1630, -720), (1632, -720), (2160, -2160), (2574, -2160), (2579, -720)]

def row98 : Integer.Sparse (Fin 3237) := [(0, -9), (32, 5), (160, -80), (225, -80), (261, -70), (503, 2160), (507, 720), (520, 720), (780, 2160), (869, 720), (1316, 4320), (1331, 2160), (1473, 2160), (1620, 2160), (1632, 720), (2160, 2160)]

def row99 : Integer.Sparse (Fin 3237) := [(0, 1), (32, -1), (160, 16), (261, 2), (697, -144), (1179, -144), (1426, -432), (1580, -432), (1611, -432), (1619, -432), (2579, -144), (2929, 1728), (2930, 1728), (2932, 576), (2940, 576), (3033, 3456), (3061, 1728), (3185, 1728), (3200, 576)]

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

def row918 : Integer.Sparse (Fin 3237) := [(0, 1662), (3, -60), (4, 15), (32, -510), (66, -240), (71, -240), (160, -1920), (222, 720), (225, -720), (256, -2160), (260, 180), (261, 2445), (1359, -12960), (1361, -12960), (1367, -12960), (1368, -12960), (1370, -25920), (1389, -12960), (1420, -12960), (1549, -12960), (1560, -12960), (1728, -12960), (1735, -12960), (1752, -12960), (1933, -12960), (2402, -12960), (2406, -12960), (2429, -12960), (2490, -12960), (2597, -12960), (2600, -25920), (2601, -25920), (2606, -12960), (2607, -12960), (2620, -12960), (2646, -12960), (2647, -25920), (2657, -12960), (2658, -12960), (2664, -12960), (2716, -25920), (2717, -25920), (2722, -25920), (2723, -25920), (2757, -12960), (2762, -25920), (2763, -12960), (2764, -12960), (2791, -25920), (2802, -12960)]

def row920 : Integer.Sparse (Fin 3237) := [(0, 150), (32, 75), (160, 240), (225, 160), (256, 80), (261, -255), (1808, -4320), (1948, -4320), (2475, -4320), (2491, -4320), (2633, -4320), (2676, -4320), (2677, -4320), (2688, -4320), (2689, -4320), (2690, -4320), (2716, -8640), (2717, -4320), (2722, -4320), (2723, -8640), (2729, -4320), (2742, -4320), (2764, -4320), (2765, -4320), (2803, -4320), (3125, 17280), (3134, 17280), (3215, 17280), (3216, 17280), (3217, 17280), (3226, 51840), (3227, 17280), (3229, 17280), (3231, 17280)]

def row921 : Integer.Sparse (Fin 3237) := [(0, -328), (32, -100), (160, 320), (255, 160), (256, 160), (261, 340), (2475, 8640), (2477, 8640), (2491, 8640), (2513, 8640), (2688, 8640), (2689, 8640), (2690, 8640), (2711, 8640), (2713, 8640), (2716, 8640), (2718, 8640), (2719, 8640), (2720, 8640), (2723, 8640), (2732, 8640), (2737, 8640), (2738, 8640), (2742, 8640), (2746, 8640)]

def row922 : Integer.Sparse (Fin 3237) := [(0, 23), (261, 25), (2557, -1440), (2558, -360), (2565, -720), (2575, -720), (2799, -1440), (2800, -360), (2801, -720), (2803, -1440)]

def row923 : Integer.Sparse (Fin 3237) := [(0, 113), (256, -80), (261, -105), (2557, -4320), (2562, -4320), (2563, -2160), (2564, -2160), (2565, -2160), (2578, -2160), (2753, -4320), (2755, -2160), (2757, -4320), (2759, -4320), (2764, -4320), (2769, -2160), (2794, -4320)]

def row924 : Integer.Sparse (Fin 3237) := [(0, 83), (32, -15), (160, 240), (225, 80), (256, 320), (261, -150), (2050, -4320), (2087, -4320), (2561, -4320), (2569, -4320), (2607, -4320), (2611, -4320), (2664, -4320), (2671, -4320), (2749, -8640), (2768, -4320), (2775, -4320), (2779, -4320), (2782, -8640), (2783, -8640), (2786, -8640), (2791, -8640), (2793, -8640), (2794, -4320), (3129, 17280), (3131, 17280), (3136, 17280), (3142, 17280), (3145, 17280), (3180, 17280), (3190, 17280), (3231, 17280), (3232, 17280), (3234, 17280), (3235, 17280)]

def row925 : Integer.Sparse (Fin 3237) := [(0, -91), (32, 35), (160, -400), (225, -240), (252, 240), (256, -320), (261, 50), (2487, 4320), (2488, 4320), (2492, 4320), (2499, 4320), (2517, 4320), (2520, 4320), (2535, 4320), (2561, 4320), (2569, 4320), (2664, 4320), (2671, 4320), (2779, 4320), (2781, 4320), (2782, 4320), (2784, 4320), (2785, 4320), (2786, 8640), (2791, 4320), (2793, 4320), (2796, 4320)]

def row926 : Integer.Sparse (Fin 3237) := [(0, 571), (32, 25), (160, 80), (256, 160), (261, 10), (1681, -4320), (1683, -4320), (1684, -4320), (1694, -4320), (1695, -4320), (1696, -4320), (1698, -8640), (1737, -4320), (1741, -4320), (1782, -4320), (1934, -4320), (1948, -4320), (1950, -4320), (2332, -4320), (2335, -4320), (2342, -4320), (2343, -4320), (2344, -4320), (2346, -8640), (2408, -4320), (2439, -4320), (2491, -4320), (2501, -4320), (2503, -4320), (2601, -4320), (2621, -4320), (2647, -4320), (2665, -4320), (2723, -8640), (2774, -8640), (2775, -4320), (2779, -4320), (2782, -8640), (2783, -8640), (2786, -8640), (2787, -8640), (2791, -8640), (2794, -4320), (2803, -4320)]

def row927 : Integer.Sparse (Fin 3237) := [(0, -343), (32, -25), (160, -80), (256, -160), (261, 50), (1681, 4320), (1683, 4320), (1684, 4320), (1698, 4320), (1737, 4320), (1741, 4320), (1782, 4320), (1934, 4320), (1950, 4320), (2332, 4320), (2335, 4320), (2346, 4320), (2491, 4320), (2601, 4320), (2621, 4320), (2723, 4320), (2774, 4320), (2775, 4320), (2782, 4320), (2783, 4320), (2786, 4320), (2787, 4320), (2791, 4320)]

def row928 : Integer.Sparse (Fin 3237) := [(0, 30), (32, 13), (160, -16), (256, -16), (261, -29), (2047, -864), (2572, -864), (2620, -864), (2621, -864), (2622, -864), (2658, -864), (2665, -864), (2669, -864), (2676, -864), (2688, -864), (2723, -1728), (2727, -1728), (2729, -864), (2742, -864), (2764, -864), (2769, -864), (2783, -864), (2786, -864), (2787, -1728), (2803, -864), (3146, 3456), (3147, 3456), (3148, 3456), (3197, 3456), (3225, 3456), (3228, 3456), (3229, 3456), (3230, 3456), (3232, 6912)]

def row929 : Integer.Sparse (Fin 3237) := [(0, -194), (32, -100), (160, -320), (225, -80), (252, 240), (255, -160), (256, -160), (261, 270), (2524, 4320), (2525, 4320), (2528, 4320), (2533, 4320), (2572, 4320), (2658, 4320), (2665, 4320), (2669, 4320), (2688, 4320), (2723, 4320), (2739, 4320), (2743, 4320), (2748, 4320), (2780, 4320), (2783, 4320), (2784, 4320), (2787, 4320), (2789, 4320)]

def row930 : Integer.Sparse (Fin 3237) := [(0, 41), (32, -5), (160, 80), (225, 40), (256, 80), (261, 70), (1753, -2160), (1758, -2160), (1761, -2160), (1934, -2160), (2081, -2160), (2087, -2160), (2097, -2160), (2177, -2160), (2437, -2160), (2449, -2160), (2450, -2160), (2501, -2160), (2555, -2160), (2556, -2160), (2561, -2160), (2573, -2160), (2607, -2160), (2611, -2160), (2664, -2160), (2671, -2160), (2674, -2160), (2682, -2160), (2685, -2160), (2691, -2160), (2693, -2160), (2697, -2160), (2698, -2160), (2705, -2160), (2717, -2160), (2722, -2160), (2729, -2160), (2742, -2160), (2763, -2160), (2783, -2160), (2786, -2160), (2791, -4320), (2793, -4320), (2794, -2160), (2839, 8640)]

def row931 : Integer.Sparse (Fin 3237) := [(0, 99), (32, 50), (160, 160), (225, 80), (256, 80), (261, -145), (1780, -2160), (1782, -2160), (1784, -2160), (1948, -2160), (2430, -2160), (2439, -2160), (2447, -2160), (2491, -2160), (2620, -2160), (2621, -2160), (2622, -2160), (2658, -2160), (2665, -2160), (2669, -2160), (2676, -2160), (2677, -2160), (2688, -2160), (2690, -2160), (2693, -2160), (2694, -2160), (2698, -2160), (2699, -4320), (2702, -2160), (2703, -4320), (2704, -4320), (2717, -2160), (2722, -2160), (2764, -4320), (2765, -2160), (2783, -2160), (2786, -2160), (2803, -2160), (2840, 8640)]

def row932 : Integer.Sparse (Fin 3237) := [(0, 24), (32, 10), (160, -40), (225, -40), (261, 10), (1815, -1080), (1950, -1080), (2047, -1080), (2481, -1080), (2503, -1080), (2572, -1080), (2606, -1080), (2610, -1080), (2657, -1080), (2668, -1080), (2676, -1080), (2688, -1080), (2717, -1080), (2722, -1080), (2723, -2160), (2729, -2160), (2742, -2160), (2766, -1080), (2783, -1080), (2786, -1080), (2803, -1080), (3126, 4320), (3136, 4320), (3143, 4320), (3144, 4320), (3181, 4320), (3215, 4320), (3218, 4320), (3222, 4320), (3226, 4320), (3230, 4320), (3232, 4320)]

def row933 : Integer.Sparse (Fin 3237) := [(0, -232), (32, -90), (160, -160), (225, 160), (255, -160), (256, -320), (261, 70), (2481, 8640), (2482, 8640), (2494, 8640), (2495, 8640), (2498, 8640), (2503, 8640), (2520, 8640), (2572, 8640), (2657, 8640), (2668, 8640), (2688, 8640), (2711, 8640), (2717, 8640), (2718, 8640), (2723, 8640), (2734, 8640), (2735, 8640), (2742, 8640), (2743, 8640), (2748, 8640), (2783, 8640)]

def row934 : Integer.Sparse (Fin 3237) := [(0, 215), (32, 20), (160, 160), (225, 80), (256, 240), (261, 5), (1370, -4320), (1373, -4320), (1376, -4320), (1422, -4320), (1562, -4320), (1680, -4320), (1684, -4320), (1696, -4320), (1933, -4320), (2331, -4320), (2335, -4320), (2344, -4320), (2490, -4320), (2601, -4320), (2621, -4320), (2647, -4320), (2665, -4320), (2676, -4320), (2688, -4320), (2717, -4320), (2722, -4320), (2763, -4320), (2764, -4320), (2782, -4320), (2783, -4320), (2786, -4320)]

def row935 : Integer.Sparse (Fin 3237) := [(0, 18), (32, 5), (160, -80), (256, -80), (261, -25), (2055, -2160), (2577, -2160), (2621, -4320), (2665, -4320), (2750, -2160), (2769, -2160), (2783, -4320), (2786, -4320), (3148, 17280), (3149, 4320), (3198, 8640), (3232, 17280)]

def row936 : Integer.Sparse (Fin 3237) := [(0, -23), (32, -10), (160, 80), (252, -120), (256, 80), (261, 5), (2533, 4320), (2534, 1080), (2539, 2160), (2577, 2160), (2665, 4320), (2783, 4320), (2784, 4320)]

def row937 : Integer.Sparse (Fin 3237) := [(0, 47), (256, -80), (261, 105), (1698, -4320), (1700, -1080), (1703, -2160), (1950, -2160), (2346, -4320), (2348, -1080), (2503, -2160), (2774, -2160), (2783, -4320), (2786, -4320)]

def row938 : Integer.Sparse (Fin 3237) := [(0, 18), (32, 5), (160, -80), (256, -80), (261, -25), (1969, -2160), (2537, -2160), (2727, -8640), (2769, -2160), (2787, -2160), (3147, 17280), (3149, 4320), (3151, 8640), (3164, 17280), (3165, 4320), (3198, 8640), (3224, 8640), (3232, 17280)]

def row939 : Integer.Sparse (Fin 3237) := [(0, -106), (32, -40), (160, 320), (256, 320), (261, 130), (274, -480), (1902, 17280), (1903, 4320), (1910, 8640), (1974, 8640), (2525, 17280), (2534, 4320), (2537, 8640), (2727, 17280), (2736, 8640), (2747, 17280)]

def row940 : Integer.Sparse (Fin 3237) := [(0, 198), (32, 30), (160, -480), (218, 720), (225, -480), (260, 180), (261, 1020), (1462, -25920), (1464, -6480), (1476, -12960), (1617, -12960), (2643, -25920), (2679, -12960), (2701, -25920), (2749, -25920), (2754, -6480), (2766, -12960)]

def row941 : Integer.Sparse (Fin 3237) := [(0, 84), (32, 35), (160, -80), (256, -80), (261, -85), (1837, -4320), (1933, -4320), (1969, -4320), (2490, -4320), (2519, -4320), (2537, -4320), (2643, -4320), (2681, -4320), (2692, -4320), (2701, -4320), (2716, -8640), (2727, -8640), (2729, -4320), (2742, -4320), (2750, -8640), (2764, -4320), (2769, -4320), (2783, -4320), (2786, -4320), (3128, 17280), (3131, 17280), (3133, 17280), (3141, 17280), (3144, 17280), (3147, 17280), (3162, 17280), (3163, 17280), (3164, 17280), (3197, 17280), (3216, 17280), (3224, 17280), (3228, 17280), (3229, 17280), (3230, 17280), (3232, 17280)]

def row942 : Integer.Sparse (Fin 3237) := [(0, -230), (32, -100), (261, 210), (274, 480), (1900, 8640), (1901, 8640), (1902, 8640), (1904, 8640), (1973, 8640), (2483, 8640), (2488, 8640), (2490, 8640), (2495, 8640), (2512, 8640), (2519, 8640), (2525, 8640), (2537, 8640), (2692, 8640), (2701, 8640), (2713, 8640), (2716, 8640), (2724, 8640), (2727, 8640), (2728, 8640), (2736, 8640), (2737, 8640), (2742, 8640), (2747, 8640), (2750, 8640)]

def row943 : Integer.Sparse (Fin 3237) := [(0, 501), (3, 60), (66, 240), (160, 1440), (218, -720), (225, 960), (256, 720), (260, -180), (261, -645), (1385, -12960), (1387, -12960), (1397, -12960), (1417, -12960), (1436, -12960), (1443, -12960), (1467, -12960), (1568, -12960), (1590, -12960), (2604, -12960), (2610, -12960), (2619, -12960), (2633, -12960), (2649, -12960), (2668, -12960), (2681, -12960), (2689, -12960), (2692, -12960), (2726, -12960), (2727, -12960), (2729, -12960), (2741, -12960), (2742, -12960), (2752, -12960), (2765, -12960), (2768, -12960)]

def row944 : Integer.Sparse (Fin 3237) := [(0, 48), (32, 25), (160, 80), (256, 80), (261, -35), (1808, -4320), (1933, -4320), (2475, -4320), (2490, -4320), (2633, -4320), (2689, -4320), (2717, -4320), (2722, -4320), (2727, -8640), (2764, -4320), (3123, 17280), (3128, 17280), (3213, 8640), (3216, 17280), (3224, 8640), (3226, 17280), (3229, 17280)]

def row945 : Integer.Sparse (Fin 3237) := [(0, -48), (32, -25), (160, -80), (256, -80), (261, 35), (2475, 4320), (2476, 4320), (2490, 4320), (2512, 4320), (2689, 4320), (2712, 2160), (2713, 4320), (2717, 4320), (2719, 4320), (2727, 4320), (2736, 2160), (2737, 4320)]

def row946 : Integer.Sparse (Fin 3237) := [(0, 117), (3, -12), (4, 3), (32, -42), (66, -96), (160, -480), (218, 144), (225, -288), (256, -288), (260, 36), (261, 366), (1358, -2592), (1361, -5184), (1368, -5184), (1388, -5184), (1548, -5184), (2597, -2592), (2600, -5184), (2606, -5184), (2646, -2592), (2657, -5184), (2716, -5184), (2717, -5184), (2722, -5184), (2756, -2592), (2762, -5184)]

def row947 : Integer.Sparse (Fin 3237) := [(0, 2), (261, 10), (2554, -180), (2558, -45), (2563, -90), (2752, -180), (2754, -45), (2756, -90), (2763, -180), (2766, -90)]

def row948 : Integer.Sparse (Fin 3237) := [(0, 114), (32, 55), (160, 80), (256, 80), (261, -95), (1752, -4320), (1755, -4320), (1760, -4320), (1808, -4320), (1815, -4320), (1837, -4320), (1933, -4320), (2429, -4320), (2438, -4320), (2446, -4320), (2475, -4320), (2481, -4320), (2490, -4320), (2519, -4320), (2606, -4320), (2610, -4320), (2633, -4320), (2643, -4320), (2657, -4320), (2668, -4320), (2681, -4320), (2689, -4320), (2692, -4320), (2693, -4320), (2698, -4320), (2699, -4320), (2701, -4320), (2703, -4320), (2716, -8640), (2717, -4320), (2722, -4320), (2723, -8640), (2727, -8640), (2729, -4320), (2742, -4320), (2764, -4320), (2803, -4320), (2840, 17280)]

def row949 : Integer.Sparse (Fin 3237) := [(0, -61), (261, -35), (2828, 1440), (2829, 360), (2830, 720), (2832, 720), (2836, 1440), (2837, 360), (2838, 720), (2839, 1440), (2840, 2160)]

def row950 : Integer.Sparse (Fin 3237) := [(0, 613), (32, 15), (160, -240), (225, -400), (261, 2910), (2097, -8640), (2554, -4320), (2556, -8640), (2571, -4320), (2642, -4320), (2643, -8640), (2684, -8640), (2700, -8640), (2701, -8640), (2704, -17280), (2733, -4320), (2749, -8640), (2752, -4320), (2756, -4320), (2760, -8640), (2763, -17280), (2766, -8640)]

def row951 : Integer.Sparse (Fin 3237) := [(0, 773), (3, -60), (4, 15), (32, 20), (66, -320), (71, -160), (160, -320), (218, 240), (222, 480), (225, 240), (256, 160), (260, 180), (261, -1080), (2081, -8640), (2553, -4320), (2555, -8640), (2570, -4320), (2633, -8640), (2635, -4320), (2677, -8640), (2689, -8640), (2690, -8640), (2694, -8640), (2702, -8640), (2715, -4320), (2726, -4320), (2741, -4320), (2751, -4320), (2761, -4320), (2762, -4320), (2764, -8640), (2765, -8640), (2768, -4320), (2788, -4320)]

def row952 : Integer.Sparse (Fin 3237) := [(0, 914), (3, -60), (4, 15), (32, -215), (66, -320), (71, -160), (160, -1360), (218, 240), (222, 480), (225, -400), (256, -1440), (260, 180), (261, 1340), (1388, -4320), (1389, -8640), (1420, -4320), (1548, -4320), (1549, -4320), (1560, -8640), (1591, -8640), (2606, -4320), (2607, -8640), (2620, -4320), (2657, -4320), (2658, -4320), (2664, -8640), (2716, -17280), (2717, -17280), (2722, -17280), (2756, -4320), (2757, -8640), (2762, -12960), (2763, -4320), (2764, -8640), (2802, -4320)]

def row953 : Integer.Sparse (Fin 3237) := [(0, 43), (32, -40), (160, -80), (225, -40), (256, -80), (261, 125), (1932, -2160), (2489, -2160), (2693, -1080), (2694, -1080), (2698, -1080), (2702, -1080), (2726, -2160), (2741, -2160), (2760, -2160), (2762, -2160), (2763, -1080), (2767, -1080), (2768, -1080), (2791, -4320), (2797, -1080), (2802, -1080), (3170, 4320), (3189, 4320), (3226, 8640), (3229, 8640), (3231, 8640)]

def row954 : Integer.Sparse (Fin 3237) := [(0, 73), (32, -5), (160, 80), (225, -80), (261, 310), (2068, -4320), (2159, -1440), (2552, -4320), (2567, -1440), (2627, -4320), (2642, -1440), (2704, -8640), (2733, -1440), (2763, -4320)]

def row955 : Integer.Sparse (Fin 3237) := [(0, 29), (32, -45), (160, -240), (225, -160), (256, -160), (261, 90), (2694, -4320), (2702, -4320), (2761, -4320), (2762, -4320), (2767, -2880), (2788, -4320), (2797, -2880), (3031, 17280), (3039, 5760), (3063, 5760), (3170, 17280), (3186, 5760), (3209, 17280), (3226, 34560)]

def row956 : Integer.Sparse (Fin 3237) := [(0, 56), (32, 5), (261, -55), (1466, -360), (1467, -360), (1468, -720), (1589, -360), (1590, -360), (1593, -360), (1608, -720), (1618, -360), (2681, -360), (2682, -720), (2692, -360), (2694, -360), (2697, -720), (2702, -360), (2726, -720), (2727, -1440), (2729, -720), (2741, -720), (2742, -720), (2751, -360), (2752, -360), (2753, -720), (2765, -720), (2768, -360), (2769, -720)]

def row957 : Integer.Sparse (Fin 3237) := [(0, 65), (32, -35), (160, 80), (225, 40), (256, 80), (261, 40), (1968, -4320), (2159, -2160), (2536, -4320), (2567, -2160), (2726, -4320), (2741, -4320), (2749, -8640), (2762, -2160), (2763, -2160), (2767, -2160), (2768, -4320), (2782, -4320), (2783, -4320), (2786, -4320), (2797, -2160), (3179, 8640), (3180, 17280), (3184, 8640), (3189, 8640), (3190, 8640), (3228, 8640), (3231, 17280), (3232, 17280)]

def row958 : Integer.Sparse (Fin 3237) := [(0, 223), (32, -15), (160, 240), (225, 240), (256, 320), (261, -450), (1796, -4320), (1836, -1440), (1895, -1440), (2023, -4320), (2046, -1440), (2351, -4320), (2369, -1440), (2518, -1440), (2566, -1440), (2568, -4320), (2672, -4320), (2673, -4320), (2699, -8640), (2703, -8640), (2767, -1440), (2768, -4320), (2794, -4320), (2797, -1440)]

def row959 : Integer.Sparse (Fin 3237) := [(0, -52), (32, 5), (160, -80), (225, -80), (256, -80), (261, 125), (2023, 2160), (2046, 720), (2351, 2160), (2369, 720), (2518, 720), (2673, 2160), (2699, 4320), (2794, 2160), (2797, 720)]

def row960 : Integer.Sparse (Fin 3237) := [(0, 47), (32, -55), (160, -80), (256, -160), (261, 230), (2635, -4320), (2642, -1440), (2694, -4320), (2702, -4320), (2715, -4320), (2733, -1440), (2760, -2880), (2761, -4320), (2788, -4320), (2802, -4320), (3047, 17280), (3054, 5760), (3063, 5760), (3228, 17280), (3229, 34560)]

def row961 : Integer.Sparse (Fin 3237) := [(0, 63), (32, -55), (160, -80), (225, -80), (261, -10), (2159, -1440), (2567, -1440), (2760, -2880), (2762, -4320), (2768, -4320), (2775, -4320), (2779, -4320), (3112, 17280), (3118, 5760), (3186, 5760), (3189, 17280), (3209, 17280), (3231, 34560)]

def row962 : Integer.Sparse (Fin 3237) := [(0, -63), (32, 55), (160, 80), (225, 80), (261, 10), (2164, 1440), (2165, 1440), (2175, 4320), (2431, 4320), (2567, 1440), (2659, 4320), (2760, 1440), (2779, 4320), (2796, 8640)]

def row963 : Integer.Sparse (Fin 3237) := [(0, 118), (225, 40), (256, -80), (261, -150), (1836, -720), (1837, -1440), (1968, -720), (2518, -720), (2519, -1440), (2536, -720), (2562, -720), (2682, -1440), (2685, -1440), (2697, -1440), (2699, -1440), (2703, -1440), (2705, -1440), (2757, -720), (2759, -720), (2767, -720), (2768, -720), (2769, -1440), (2794, -2160), (2797, -720)]

def row964 : Integer.Sparse (Fin 3237) := [(0, 751), (32, 5), (160, -80), (225, 80), (256, -320), (261, 50), (1780, -4320), (1781, -4320), (1782, -8640), (1918, -4320), (1919, -4320), (1920, -4320), (1948, -8640), (2430, -4320), (2439, -8640), (2458, -4320), (2460, -4320), (2491, -8640), (2571, -4320), (2620, -4320), (2621, -8640), (2658, -4320), (2665, -8640), (2763, -4320), (2775, -8640), (2779, -8640), (2783, -8640), (2786, -8640), (2791, -17280), (2794, -4320), (2802, -4320), (2803, -8640)]

def row965 : Integer.Sparse (Fin 3237) := [(0, 8), (32, -5), (261, 15), (2682, -360), (2693, -360), (2697, -360), (2698, -360), (2717, -360), (2722, -360), (2729, -360), (2742, -360), (2791, -720), (2793, -1440), (2794, -360), (2802, -360), (3106, 1440), (3107, 1440), (3108, 1440), (3117, 1440), (3124, 1440), (3125, 1440), (3134, 1440), (3174, 1440), (3194, 1440), (3205, 1440), (3206, 1440), (3212, 1440), (3223, 1440), (3225, 1440), (3229, 2880), (3233, 1440), (3235, 1440), (3236, 1440)]

def row966 : Integer.Sparse (Fin 3237) := [(0, -292), (32, 300), (160, 640), (225, 160), (256, 480), (261, -880), (274, -480), (1806, 8640), (1807, 8640), (1811, 8640), (1834, 8640), (1930, 8640), (2412, 8640), (2415, 8640), (2433, 8640), (2527, 8640), (2648, 8640), (2650, 8640), (2661, 8640), (2697, 8640), (2698, 8640), (2725, 8640), (2737, 8640), (2770, 8640), (2771, 8640), (2776, 8640), (2781, 8640), (2792, 8640), (2793, 8640)]

def row967 : Integer.Sparse (Fin 3237) := [(0, -156), (3, 48), (4, -6), (32, 150), (66, 96), (68, 96), (160, 864), (162, 192), (222, -288), (225, 384), (251, -288), (255, 96), (256, 576), (260, -72), (261, -504), (1749, 5184), (1751, 5184), (1754, 5184), (1773, 5184), (1967, 5184), (2461, 5184), (2465, 5184), (2477, 5184), (2513, 5184), (2605, 5184), (2608, 5184), (2617, 5184), (2721, 5184), (2722, 5184), (2725, 5184), (2729, 5184), (2739, 5184), (2777, 5184), (2789, 5184), (2790, 5184), (2791, 5184), (2792, 5184), (2793, 5184)]

def row968 : Integer.Sparse (Fin 3237) := [(0, 1007), (3, -60), (4, 15), (32, -110), (66, -80), (71, -400), (160, -160), (222, 240), (225, -160), (256, 160), (260, 180), (261, 340), (273, 480), (1808, -8640), (1810, -4320), (1932, -4320), (2475, -8640), (2480, -4320), (2489, -4320), (2553, -4320), (2674, -8640), (2676, -8640), (2688, -8640), (2691, -8640), (2693, -8640), (2698, -8640), (2764, -8640), (2775, -4320), (2779, -4320), (2782, -8640), (2798, -4320), (2802, -8640), (2803, -8640)]

def row969 : Integer.Sparse (Fin 3237) := [(0, 1049), (3, -60), (4, 15), (32, -100), (66, -80), (71, -400), (160, -320), (222, 240), (225, -160), (256, -480), (260, 180), (261, 620), (273, 480), (1752, -4320), (1753, -8640), (1780, -4320), (2429, -4320), (2430, -4320), (2437, -8640), (2570, -4320), (2606, -4320), (2607, -8640), (2620, -4320), (2657, -4320), (2658, -4320), (2664, -8640), (2717, -8640), (2722, -8640), (2757, -4320), (2762, -4320), (2791, -17280), (2794, -4320), (2801, -8640), (2803, -8640)]

def row970 : Integer.Sparse (Fin 3237) := [(0, 2118), (3, -60), (4, 15), (32, -165), (66, -240), (71, -240), (160, -240), (222, 720), (225, -240), (256, -480), (260, 180), (261, -1710), (1750, -25920), (1756, -12960), (1775, -12960), (1968, -12960), (2414, -25920), (2416, -12960), (2445, -12960), (2536, -12960), (2604, -25920), (2609, -12960), (2618, -12960), (2649, -25920), (2651, -12960), (2667, -12960), (2677, -25920), (2682, -25920), (2690, -25920), (2697, -25920), (2726, -12960), (2729, -25920), (2741, -12960), (2742, -25920), (2757, -12960), (2761, -12960), (2762, -12960), (2764, -25920), (2768, -12960), (2788, -12960), (2793, -51840), (2794, -12960)]

def row971 : Integer.Sparse (Fin 3237) := [(0, -1251), (3, 60), (4, -15), (66, 240), (71, 240), (222, -720), (260, -180), (261, 1050), (1750, 25920), (1756, 12960), (1775, 12960), (1968, 12960), (2604, 25920), (2609, 12960), (2618, 12960), (2682, 25920), (2690, 25920), (2726, 12960), (2742, 25920), (2761, 12960), (2762, 12960), (2768, 12960), (2793, 25920)]

def row972 : Integer.Sparse (Fin 3237) := [(0, 88), (32, -60), (225, 40), (256, -80), (261, 300), (2682, -4320), (2684, -2160), (2697, -4320), (2700, -2160), (2717, -4320), (2722, -4320), (2726, -2160), (2741, -2160), (2763, -2160), (2782, -4320), (2791, -8640), (2793, -8640), (2794, -2160), (2802, -4320), (3169, 8640), (3170, 8640), (3174, 17280), (3189, 8640), (3222, 8640), (3228, 8640), (3229, 17280), (3235, 17280), (3236, 17280)]

def row973 : Integer.Sparse (Fin 3237) := [(0, -206), (32, 270), (160, 1440), (225, 240), (255, 320), (256, 960), (261, -1260), (274, -480), (1923, 4320), (1924, 4320), (1930, 8640), (1957, 4320), (2697, 8640), (2700, 4320), (2726, 4320), (2735, 4320), (2737, 8640), (2780, 4320), (2781, 8640), (2782, 4320), (2792, 8640), (2793, 8640)]

def row974 : Integer.Sparse (Fin 3237) := [(0, 131), (32, -15), (160, 240), (225, 80), (256, 320), (261, 90), (2097, -4320), (2556, -4320), (2682, -4320), (2685, -4320), (2697, -4320), (2705, -4320), (2729, -8640), (2742, -8640), (2763, -4320), (2783, -4320), (2786, -4320), (2791, -8640), (2793, -17280), (2794, -8640), (3134, 17280), (3135, 17280), (3136, 17280), (3174, 17280), (3175, 17280), (3183, 17280), (3194, 34560), (3229, 17280), (3232, 17280), (3233, 17280), (3234, 17280), (3235, 17280), (3236, 34560)]

def row975 : Integer.Sparse (Fin 3237) := [(0, -166), (32, 30), (160, -640), (225, -160), (255, -160), (256, -480), (261, -20), (1930, 4320), (1931, 4320), (1935, 4320), (1945, 4320), (1967, 4320), (2513, 4320), (2520, 4320), (2527, 4320), (2556, 4320), (2697, 4320), (2705, 4320), (2729, 4320), (2781, 4320), (2784, 4320), (2785, 4320), (2786, 4320), (2789, 4320), (2790, 4320), (2791, 4320), (2792, 8640), (2793, 4320)]

def row976 : Integer.Sparse (Fin 3237) := [(0, 57), (32, 7), (160, -16), (256, 32), (261, -62), (1775, -864), (1776, -864), (1777, -864), (1784, -864), (1979, -864), (2416, -864), (2418, -864), (2447, -864), (2538, -864), (2618, -864), (2619, -864), (2622, -864), (2651, -864), (2669, -864), (2729, -864), (2742, -864), (2761, -864), (2764, -864), (2769, -864), (2788, -864), (2793, -1728)]

def row977 : Integer.Sparse (Fin 3237) := [(0, 329), (3, -60), (4, 15), (32, -220), (66, -80), (71, -400), (160, -320), (222, 240), (256, -160), (260, 180), (261, 260), (273, 480), (2553, -4320), (2554, -4320), (2557, -8640), (2570, -4320), (2757, -4320), (2759, -4320), (2764, -8640), (2798, -4320), (2799, -8640), (2801, -8640), (2802, -12960), (2803, -8640)]

def row978 : Integer.Sparse (Fin 3237) := [(0, 37), (32, -6), (256, -16), (261, 21), (1734, -432), (1735, -432), (1737, -432), (1780, -432), (1948, -432), (2402, -432), (2408, -432), (2430, -432), (2491, -432), (2600, -432), (2601, -432), (2620, -432), (2647, -432), (2658, -432), (2717, -432), (2722, -432), (2774, -432), (2783, -432), (2786, -432), (2791, -432), (2794, -432), (2802, -432)]

def row979 : Integer.Sparse (Fin 3237) := [(0, 19), (32, -25), (160, -80), (225, -40), (256, -80), (261, 80), (2760, -720), (2761, -1080), (2762, -1080), (2767, -720), (2775, -1080), (2779, -1080), (2788, -1080), (2791, -4320), (2797, -720), (2802, -1080), (2839, 1440)]

def row980 : Integer.Sparse (Fin 3237) := [(0, 64), (32, -60), (225, 40), (256, -80), (261, 180), (2046, -2160), (2566, -2160), (2607, -4320), (2609, -2160), (2664, -4320), (2667, -2160), (2726, -4320), (2741, -4320), (2768, -2160), (2782, -8640), (2783, -4320), (2786, -4320), (2802, -4320), (3141, 8640), (3142, 17280), (3179, 8640), (3222, 8640), (3228, 25920), (3235, 17280)]

def row981 : Integer.Sparse (Fin 3237) := [(0, -63), (32, 105), (160, 720), (225, 280), (252, -240), (255, 160), (256, 560), (261, -460), (2483, 2160), (2484, 2160), (2487, 4320), (2566, 2160), (2664, 4320), (2667, 2160), (2735, 2160), (2740, 4320), (2780, 2160), (2781, 4320), (2782, 4320), (2786, 4320)]

def row982 : Integer.Sparse (Fin 3237) := [(0, 63), (32, -11), (160, -16), (256, 32), (261, -14), (1680, -1728), (1681, -864), (1694, -864), (1932, -864), (2331, -1728), (2332, -864), (2342, -864), (2489, -864), (2676, -1728), (2688, -1728), (2723, -1728), (2775, -864), (2779, -864), (2783, -1728), (2786, -1728), (2802, -864)]

def row983 : Integer.Sparse (Fin 3237) := [(0, 657), (3, 60), (32, 15), (66, 240), (160, -240), (218, -720), (225, -480), (260, -180), (261, 2970), (1461, -12960), (1462, -25920), (1471, -12960), (1616, -12960), (2642, -12960), (2643, -25920), (2679, -25920), (2684, -12960), (2700, -12960), (2701, -25920), (2733, -12960), (2749, -25920), (2750, -25920), (2752, -12960), (2763, -12960), (2766, -25920)]

def row984 : Integer.Sparse (Fin 3237) := [(0, 107), (32, -95), (160, -400), (225, -320), (256, -160), (261, 130), (1932, -4320), (2489, -4320), (2682, -8640), (2684, -4320), (2697, -8640), (2700, -4320), (2729, -8640), (2742, -8640), (2749, -8640), (2762, -8640), (2791, -17280), (2794, -4320), (3142, 34560), (3143, 17280), (3146, 17280), (3155, 17280), (3156, 17280), (3159, 34560), (3189, 17280), (3226, 34560), (3229, 34560), (3231, 34560)]

def row985 : Integer.Sparse (Fin 3237) := [(0, -109), (32, 195), (160, 1040), (225, 320), (255, 160), (256, 640), (261, -620), (274, -480), (1888, 4320), (1889, 4320), (1893, 8640), (1957, 4320), (2487, 8640), (2489, 4320), (2494, 4320), (2524, 4320), (2697, 8640), (2700, 4320), (2719, 8640), (2725, 8640), (2729, 8640), (2746, 8640), (2749, 4320)]

def row986 : Integer.Sparse (Fin 3237) := [(0, 1548), (3, -240), (4, 15), (32, -195), (66, -1200), (160, -2640), (218, 1440), (222, 1440), (225, -720), (256, 480), (260, 720), (261, -1890), (1385, -25920), (1392, -12960), (1415, -12960), (1436, -25920), (1438, -12960), (1466, -12960), (1567, -12960), (1589, -12960), (2604, -25920), (2609, -12960), (2618, -12960), (2633, -25920), (2635, -12960), (2649, -25920), (2651, -12960), (2667, -12960), (2681, -25920), (2689, -25920), (2692, -25920), (2715, -12960), (2726, -12960), (2727, -51840), (2729, -25920), (2741, -12960), (2742, -25920), (2751, -12960), (2758, -12960), (2762, -12960), (2765, -25920), (2768, -25920)]

def row987 : Integer.Sparse (Fin 3237) := [(0, -269), (3, 60), (32, 25), (66, 240), (160, 560), (218, -240), (222, -480), (225, 160), (260, -180), (261, 250), (1436, 8640), (1438, 4320), (1466, 4320), (1567, 4320), (2633, 8640), (2635, 4320), (2649, 8640), (2651, 4320), (2667, 4320), (2692, 8640), (2727, 8640), (2741, 4320), (2742, 8640), (2758, 4320), (2765, 8640)]

def row988 : Integer.Sparse (Fin 3237) := [(0, 115), (32, -75), (160, 240), (225, 160), (256, 160), (261, 30), (1836, -4320), (1968, -4320), (2518, -4320), (2536, -4320), (2642, -4320), (2717, -8640), (2722, -8640), (2726, -8640), (2733, -4320), (2741, -8640), (2749, -8640), (2768, -8640), (2782, -17280), (2802, -4320), (3129, 34560), (3132, 17280), (3167, 17280), (3168, 17280), (3179, 34560), (3215, 34560), (3225, 34560), (3228, 51840)]

def row989 : Integer.Sparse (Fin 3237) := [(0, 267), (3, -60), (4, 15), (32, -170), (66, -320), (71, -160), (160, -1120), (218, 240), (222, 480), (225, -400), (256, -160), (260, 180), (261, -100), (2553, -4320), (2557, -8640), (2562, -4320), (2751, -4320), (2752, -4320), (2753, -8640), (2757, -8640), (2758, -4320), (2762, -8640), (2764, -8640), (2765, -8640), (2768, -4320)]

def row990 : Integer.Sparse (Fin 3237) := [(0, 47), (32, -55), (160, -80), (256, -160), (261, 230), (1810, -4320), (1836, -1440), (2480, -4320), (2518, -1440), (2635, -4320), (2642, -1440), (2715, -4320), (2717, -8640), (2722, -8640), (2726, -4320), (2733, -1440), (2741, -4320), (2767, -1440), (2797, -1440), (2802, -4320), (2839, 5760)]

def row991 : Integer.Sparse (Fin 3237) := [(0, -17), (261, 5), (2827, 60), (2828, 180), (2831, 60), (2835, 60), (2836, 180), (2838, 180), (2839, 300), (2840, 360)]

def row992 : Integer.Sparse (Fin 3237) := [(0, 1101), (3, -60), (4, 15), (66, -480), (218, 720), (225, 480), (260, 180), (261, 5820), (2679, -51840), (2684, -51840), (2700, -51840), (2749, -51840), (2756, -12960), (2763, -51840)]

def row993 : Integer.Sparse (Fin 3237) := [(0, -19), (261, -5), (2838, 360), (2839, 480)]

def row994 : Integer.Sparse (Fin 3237) := [(351, 1), (576, 3), (677, 1), (697, 1), (2832, -1)]

def row995 : Integer.Sparse (Fin 3237) := [(521, 1), (1074, 3), (1178, 1), (1180, 1), (2820, -1)]

def row996 : Integer.Sparse (Fin 3237) := [(1175, 3), (1178, 2), (1180, 1), (2820, -1)]

def row997 : Integer.Sparse (Fin 3237) := [(321, 1), (554, 2), (591, 1), (641, 1), (659, 1), (2831, -1)]

def row998 : Integer.Sparse (Fin 3237) := [(516, 1), (1063, 2), (1175, 1), (1178, 2), (2820, -1)]

def row999 : Integer.Sparse (Fin 3237) := [(478, 2), (481, 1), (491, 1), (503, 1), (1151, 1), (2817, -1)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Targets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def targetRow0 : Integer.Sparse (Fin 3237) := [(0, 19641545570140655616000), (1, 393661292632473600000), (2, -176614741297612800000), (3, 3221049461020876800000), (4, 365717504568729600000), (5, -668797982060544000000), (6, 3497224054947840000000), (7, 1776106015617024000000), (8, 3635458356805632000000), (9, -8587699706363904000000), (10, 10815717612581683200000), (12, -8918577379314892800000), (13, -7410130929421516800000), (14, 8419210088841216000000), (15, 13348031491591372800000), (16, -13208691003295334400000), (17, 4745802201477120000000), (19, 2344146906415104000000), (20, -4304761391185920000000), (21, -464566913608089600000), (23, -2552961633494630400000), (24, -45071977043939328000000), (26, -75222115850649600000), (27, 3088303514556825600000), (29, 3216637014287155200000), (31, 16182381785549414400000), (32, 4127895532686385152000), (34, 4283407023294873600000), (35, 3692799467642880000000), (37, 581673332072448000000), (61, -7522157156548608000000), (66, 4614860267355340800000), (68, 20300984533831680000000), (71, -3743296719276441600000), (149, -23459956324245504000000), (150, -5779978416672768000000), (153, 9185931342714470400000), (154, 11504122430924390400000), (156, 34702576396546867200000), (159, 20844440076334694400000), (160, 85294320795494350848000), (162, 37752633912513429504000), (163, 5071126617627033600000), (164, 2895341101225574400000), (165, 8392474405866700800000), (212, -15476971187994624000000), (213, -3484357479751680000000), (215, -1563346487756390400000), (217, 15472899725952614400000), (218, 10762160834550988800000), (219, -12374076546168422400000), (222, 18372170846144102400000), (224, 31850438803874611200000), (225, 19336696563874185216000), (251, 6418437993883238400000), (252, -13061544614963970048000), (255, 21002351171644588032000), (256, 19898102156931661824000), (260, 1418716175772672000000), (261, 1270790013347850240000), (273, -4680882943930368000000), (274, -7435683545859588096000), (311, -654308882759024640000), (312, -2282493232765992960000)]

def targetRow1 : Integer.Sparse (Fin 3237) := [(313, 654308882759024640000), (314, 877592856526848000000), (315, 877447660307742720000), (316, 607591276892651520000), (317, 2282493232765992960000), (318, -113253321790586880000), (319, -2325444766551244800000), (320, -878028445184163840000), (321, 4950070676784414720000), (322, -947351242264412160000), (323, -877883248965058560000), (324, -544816666760970240000), (325, 2291676713032089600000), (331, -28541892592926720000), (333, -1211529171307069440000), (334, 344588552322416640000), (335, 28541892592926720000), (337, 533546803510640640000), (338, 6690208535414046720000), (339, -2453660793490636800000), (340, 1441480432653434880000), (341, 2300979745408942080000), (342, -1054181617875025920000), (344, -9473152863350292480000), (345, 18388973290326589440000), (346, -584459388199895040000), (347, -2602745435968634880000), (348, 677982367796428800000), (349, 1801435404238848000000), (350, -2365767237453742080000), (351, 3002873618910412800000), (352, 1287214867623444480000), (353, 3163253859043246080000), (354, 9267211259630714880000), (355, 365728146625658880000), (356, -820112129438515200000), (357, -1258494730418257920000), (358, -363229471392399360000), (360, 4002258833827430400000), (361, -860150167449108480000), (362, 363229471392399360000), (363, 1355923199361024000000), (364, -1355923199361024000000), (365, -3620046943302451200000), (367, 4614435349529886720000), (368, -4581648092858941440000), (369, -1883613935960064000000), (370, -3999431119401123840000), (371, 5023829814312960000000), (372, 5237719375993896960000), (373, -3501219910680576000000), (374, -5023829814312960000000), (375, 2600840819146752000000), (376, -7838560195140648960000), (377, 3501219910680576000000), (379, 892167378500321280000), (380, 315973519843000320000), (552, 8659257895151861760000), (554, 7407336363717427200000), (557, 8137792988223897600000), (563, 842806262366208000000), (569, -941481721225543680000), (570, -4522163694065418240000), (571, 862331180804997120000)]

def targetRow2 : Integer.Sparse (Fin 3237) := [(572, -2281209943794647040000), (573, -842806262366208000000), (574, 1048155974782156800000), (576, -3501622812129361920000), (577, -690110044530278400000), (579, -5644648033344552960000), (580, -3110224913045913600000), (584, 5755499567677440000000), (585, 5755499567677440000000), (586, 4959624732475392000000), (589, -7458564352880148480000), (590, -5755499567677440000000), (591, 7458564352880148480000), (592, -4959624732475392000000), (593, -5755499567677440000000), (594, -3501219910680576000000), (638, -2976678613712240640000), (641, -4206296272205905920000), (652, 84218592777338880000), (654, -1011243447920885760000), (657, -2007773678972436480000), (659, 10725266364412723200000), (660, -13781464017158799360000), (662, 1567784528782295040000), (663, 927024855143546880000), (664, 1191593947134689280000), (671, 6300739362226176000000), (674, -3750701327642787840000), (676, -6300739362226176000000), (677, 3750701327642787840000), (695, -8631272678361661440000), (697, 7331333818189086720000), (700, -2107338916154572800000), (715, 94866766992506880000), (716, -26389657073487052800000), (717, -8810814575497052160000), (719, -1573216023167631360000), (720, -1126879414384066560000), (721, -250586732209766400000), (722, 4772950974038016000000), (723, -1307377367220879360000), (724, 6812136157446144000000), (725, -8762782347893145600000), (729, 416003421044736000000), (730, 3128439995443445760000), (732, 331078441437757440000), (733, 19378969510926090240000), (734, -9464678117613895680000), (735, 5641023726228602880000), (736, -1759585423361310720000), (737, 1307514346489774080000), (738, 3771399734927032320000), (739, -4459227814998835200000), (741, 467378502645841920000), (742, -19215558570607902720000), (743, -10083993537718517760000), (744, 5594674980160143360000), (745, 871459791106867200000), (746, 5137435020224102400000), (747, -5549518414241464320000), (748, -2210692257679933440000), (749, 2991047260449669120000), (750, 167779287760896000000), (752, -54778388874854400000)]

def targetRow3 : Integer.Sparse (Fin 3237) := [(753, 54778388874854400000), (754, 598839592845312000000), (755, -3796503149893386240000), (757, -2713512723987824640000), (759, 3773107777016954880000), (760, -4033883256599347200000), (763, -1465158899028787200000), (764, 5499042155628134400000), (765, 4433171053215744000000), (766, 6851070957020774400000), (767, 606438917347737600000), (801, 934778270036459520000), (804, -1029645037028966400000), (805, 250586732209766400000), (806, 18978681323195596800000), (808, 11351689807634104320000), (810, 972527074748006400000), (819, -6722247552986972160000), (820, -416003421044736000000), (821, 3252202435368714240000), (822, 12119156027369717760000), (823, 6722247552986972160000), (825, -2570828363354603520000), (826, -12547178408576286720000), (827, 8753467817805742080000), (828, -3100873301337047040000), (829, -2614211302075269120000), (831, 7725885129934110720000), (832, -19348453924951818240000), (843, -7062722889655910400000), (844, -9103216750304624640000), (845, 7062722889655910400000), (847, 8502527801884999680000), (849, -8079242612869693440000), (851, -5076859302087229440000), (863, -2206050538624450560000), (864, 2219882239269273600000), (865, 4459227814998835200000), (866, 11729049453615513600000), (867, 2206050538624450560000), (869, 5575466278860226560000), (871, -6047328798324817920000), (873, -626180907745935360000), (874, 5977466481711513600000), (875, 3501622812129361920000), (876, -9579839035999518720000), (877, 7341542882196848640000), (878, -4432587559454638080000), (879, -3032742142629642240000), (880, 11886766950399344640000), (881, -10548491592982855680000), (882, 9579839035999518720000), (883, -4933072605979607040000), (884, -8886421804453724160000), (885, -8635312347795947520000), (886, 277114839928012800000), (887, -5341116330562682880000), (888, -2299907207666073600000), (889, -819339736118722560000), (890, -3493413807980544000000), (891, 7641023538228756480000), (892, 8698253102854963200000), (893, 7361272231133184000000), (894, 3435031202884485120000)]

def targetRow4 : Integer.Sparse (Fin 3237) := [(895, -1895122181062656000000), (896, 4158977745420288000000), (898, 1542086242739159040000), (910, -1899117244195799040000), (911, 2667259420956426240000), (913, -3750701327642787840000), (914, 1899117244195799040000), (916, 8859486641663508480000), (919, -11526746062619934720000), (923, 4656026210537963520000), (925, -3478154931439534080000), (927, -2299907207666073600000), (930, -2356119002871889920000), (936, -22276992136265072640000), (938, -17269758213677383680000), (947, 847409560407244800000), (948, -3245969833485926400000), (950, 39708998817546240000), (977, -1056230257065984000000), (978, -1423280520010137600000), (980, -1951341470849433600000), (981, 1056230257065984000000), (984, 1423280520010137600000), (986, -2210913934743306240000), (987, -2862630613510520832000), (988, -1812234680041734144000), (989, 807931683631005696000), (990, 279082176459964416000), (991, 1951341470849433600000), (992, 1532149313286832128000), (996, 3125626258862112768000), (998, 1398340775856439296000), (999, 1978196107527585792000), (1002, 3237439447258103808000), (1004, -115736953684230144000), (1005, -190397481621258240000), (1006, -179029231679176704000), (1007, -24315273996926976000), (1008, 513372727945986048000), (1009, 3726326584597413888000), (1010, 92042023309737984000), (1016, 299269579737268224000), (1108, -1090667657931522048000), (1109, -1101980502152183808000), (1111, -735052166107693056000), (1112, -615325865037004800000), (1116, 441343231347916800000), (1118, 2798915153550114816000), (1119, 4204277593279561728000), (1122, 4390161007521300480000), (1124, 604529641244196864000), (1125, 910860777696264192000), (1126, 789405404560883712000), (1127, -120789168095232000000), (1128, 1305313133883752448000), (1129, 3666193326655340544000), (1135, 888021087364841472000), (1136, 550098197290156032000), (1137, -902368496446341120000), (1138, -1069052130648391680000), (1139, 2007627038014832640000), (1140, 583395049348005888000), (1144, -2010373847085219840000), (1146, -4752834733161381888000)]

def targetRow5 : Integer.Sparse (Fin 3237) := [(1147, -4818691431020888064000), (1148, -3378878307861331968000), (1149, -6227807807028068352000), (1150, -2138368756797407232000), (1151, 1926014843785052160000), (1152, -1541521449311993856000), (1153, 1386207265990901760000), (1154, 1717512314662158336000), (1155, -4810412754357977088000), (1159, 3751773612556419072000), (1160, -95615204742070272000), (1161, 2302759193699155968000), (1162, 2459234748121546752000), (1166, 4524755554931834880000), (1168, 119212994511765504000), (1169, -8626840581832704000), (1170, -554123003977138176000), (1171, -2769188286440669184000), (1172, -3563661364114489344000), (1173, -1117582666619682816000), (1174, 4393837063364345856000), (1175, -722047208039055360000), (1180, -474172475731476480000), (1202, 654308882759024640000), (1203, -4566900924634890240000), (1204, -6742174334468751360000), (1205, 2282493232765992960000), (1206, 3731415152240885760000), (1207, 673420605987225600000), (1208, 8275744746720460800000), (1209, 8393450481675141120000), (1210, 5418404332170117120000), (1214, 6265573704801976320000), (1215, 28541892592926720000), (1216, 2797448960684851200000), (1217, 3885170543988572160000), (1218, -9608222007357603840000), (1219, 9318508415649054720000), (1220, -4955053941050572800000), (1221, -3537875996458352640000), (1222, -3345967769848381440000), (1223, 4908991524093296640000), (1224, -11721265473473740800000), (1225, 6324490501957877760000), (1226, 2579448756790886400000), (1227, -8001262491225292800000), (1228, 8788236653722337280000), (1229, -1747607698444124160000), (1230, -7591910646227927040000), (1231, -10541826291919749120000), (1232, -629645571257794560000), (1233, 1301309194638458880000), (1234, 1098658614922444800000), (1235, -1301309194638458880000), (1236, 819808734353817600000), (1237, 3329639154745344000000), (1238, 2357878242882355200000), (1239, -1098658614922444800000), (1240, -750480790392668160000), (1241, 6755524079380070400000), (1242, 2387485449525657600000), (1243, 4222772882708889600000), (1244, -971893105435607040000), (1335, -478232461800898560000)]

def targetRow6 : Integer.Sparse (Fin 3237) := [(1340, -23934621521018880000), (1341, 2241235474277990400000), (1342, 5347929085248798720000), (1343, 842806262366208000000), (1345, 2206413845208760320000), (1346, 3110224913045913600000), (1348, 6990515310978662400000), (1351, 2052530594103951360000), (1352, -1235015743301222400000), (1353, 4959624732475392000000), (1354, 5755499567677440000000), (1355, 5338073982173184000000), (1379, -3936013149156802560000), (1388, -2983567758946467840000), (1389, 755963843883171840000), (1391, 2983567758946467840000), (1392, 88617370024673280000), (1394, -4644957617419714560000), (1395, 3018336835652812800000), (1397, 590858676786954240000), (1398, -2441576368615587840000), (1406, 4121680737526087680000), (1408, 6300739362226176000000), (1420, -2470341383010385920000), (1422, 2470341383010385920000), (1424, -2837840598442967040000), (1426, -3893099630053294080000), (1449, -2282493232765992960000), (1450, -18920168420746199040000), (1451, -27244411052347883520000), (1453, 14205848185641369600000), (1455, 15839955060530872320000), (1465, -28541892592926720000), (1466, -338218339097640960000), (1467, 283347893291581440000), (1468, 5704108413360537600000), (1469, -18375094409940172800000), (1470, 5542318650230046720000), (1471, -14180570318501314560000), (1473, -3684095090420613120000), (1474, -757176972741181440000), (1476, -12013936625481154560000), (1477, -1563346111522406400000), (1491, 1418945220960583680000), (1492, -1418945220960583680000), (1493, 11767743613933977600000), (1494, 4056479869678387200000), (1495, -40767630952366080000), (1497, 8053752549762662400000), (1499, -1056230257065984000000), (1501, -1423280520010137600000), (1503, 1234719933093642240000), (1504, 747433945254592512000), (1505, -1041522169018318848000), (1506, -1400262241941061632000), (1507, -1951341470849433600000), (1508, -3528479019960631296000), (1512, -5084299705354813440000), (1513, 415726753622261760000), (1514, -199802494476877824000), (1517, -1958086160293036032000), (1519, 350247195718189056000), (1520, 460809475344433152000), (1521, 1082771078483017728000)]

def targetRow7 : Integer.Sparse (Fin 3237) := [(1522, 104801980817866752000), (1523, -4082980870490554368000), (1530, -888215115745198080000), (1531, -1086333153488142336000), (1534, -2488877088999211008000), (1535, -1039334509865336832000), (1537, -2644281324676841472000), (1538, 382802499623190528000), (1539, 80987525421465600000), (1540, -2480383209507323904000), (1546, 1069052130648391680000), (1547, -535625493262368768000), (1550, 2550756900341809152000), (1552, 506714469983059968000), (1553, 2281683348482162688000), (1554, 4171042250963288064000), (1555, 3716334068831354880000), (1556, -1758049717505163264000), (1557, -529608735311265792000), (1558, -2923000637003661312000), (1559, -968581412641898496000), (1563, -1075562447389065216000), (1564, 3118020017674125312000), (1565, 3417517613264928768000), (1566, -164392035143712768000), (1570, 6106405275203272704000), (1572, 543996082382635008000), (1573, 1698881328169353216000), (1574, -2422443967567626240000), (1575, -2652931479726194688000), (1576, 454996272018161664000), (1581, 522094469787942912000), (1582, 825412766634344448000), (1583, -7143996310767009792000), (1584, 5281412168984297472000), (1585, 8991466736109355008000), (1586, 1167171979199643648000), (1587, -11939427307487232000), (1588, -912884097845035008000), (1591, 5842413970256166912000), (1592, -10405086036950384640000), (1593, 1027025879634542592000), (1594, 14561556817950277632000), (1595, -13271920026826309632000), (1596, -2840232254671945728000), (1597, -2254308298937597952000), (1598, 6385220328544468992000), (1599, 6295106507412602880000), (1600, -1717100482923528192000), (1601, -11806284324964663296000), (1602, 3977835312798498816000), (1603, 13423761248418791424000), (1604, -3060986888631877632000), (1605, 356540332144066560000), (1606, -285682392053710848000), (1607, -2232992392359837696000), (1610, 7630898178757754880000), (1611, -18920842427374239744000), (1612, 2456191162674708480000), (1613, 620385158666649600000), (1614, 1530801552859987968000), (1615, 11930424302148452352000), (1618, 2987453130309107712000), (1619, -1108983474720866304000)]

def targetRow8 : Integer.Sparse (Fin 3237) := [(1620, -1604990175025692672000), (1621, 4794515628466765824000), (1622, 10806536498743738368000), (1623, -328449504969621504000), (1624, 1069657792115834880000), (1625, 3942379037195698176000), (1626, 88491352709136384000), (1627, 1402778741635547136000), (1631, -757011477946171392000), (1632, -8727219315144916992000), (1641, -5775400208422010880000), (1645, 1409374911961497600000), (1648, -1021462625098137600000), (1649, 8792971061782118400000), (1651, 1021462625098137600000), (1653, 2042925250196275200000), (1654, 6349509219129753600000), (1655, -1957928575441305600000), (1656, -5831241247610634240000), (1657, -4592195406267678720000), (1658, -8792971061782118400000), (1660, -1021462625098137600000), (1661, -15267702809682247680000), (1662, 3811111984406200320000), (1663, 54778388874854400000), (1664, -54778388874854400000), (1665, -598839592845312000000), (1666, -2122040394523607040000), (1668, 14499441893476270080000), (1669, -4008567374777548800000), (1671, -3201531558440140800000), (1672, 7210098933217689600000), (1673, -4433171053215744000000), (1674, -9916201969680384000000), (1707, 5684917680995696640000), (1709, -3022934715924480000000), (1710, -2089015568665804800000), (1712, 5559732986314752000000), (1713, -3513264514950758400000), (1714, 19962365120110264320000), (1715, 14124724583912570880000), (1716, 762973624782028800000), (1717, 2089015568665804800000), (1718, -4285922492777103360000), (1719, 5339288646065848320000), (1721, -29125569354242457600000), (1722, -4666690457468928000000), (1723, -1089057424637952000000), (1724, -27156418471526400000), (1725, 4167404634193920000000), (1726, -6201565287992524800000), (1743, -669848715789926400000), (1744, 5402275542460661760000), (1746, 669848715789926400000), (1752, -21951447043276800000), (1753, -12811011857783193600000), (1755, 3044886162967756800000), (1756, 10730200326977617920000), (1758, -7075268186112000000000), (1759, -10132091952404889600000), (1760, 3036144140609126400000), (1761, 12048038233001164800000), (1766, 882109921738752000000), (1767, 421979070165811200000)]

def targetRow9 : Integer.Sparse (Fin 3237) := [(1769, 2247947368157675520000), (1771, -7786684812636979200000), (1780, 4693700295180288000000), (1782, -8251961190668697600000), (1783, -4629005356695552000000), (1784, 20072224660871577600000), (1786, 4382870405576785920000), (1787, 3829273250294661120000), (1789, -46570423131832320000), (1790, 94866766992506880000), (1792, -1138001372530606080000), (1803, -1139201814778675200000), (1808, -5874441005529169920000), (1810, -762973624782028800000), (1811, -827530229555527680000), (1812, 3350500907776081920000), (1814, -1308617765518049280000), (1815, -8081533245759160320000), (1819, 54778388874854400000), (1822, -54778388874854400000), (1824, 3475493000755937280000), (1825, 7730575112285061120000), (1834, 2089015568665804800000), (1836, -878316128737689600000), (1837, 9764819380324270080000), (1838, -2089015568665804800000), (1841, 6525212987851407360000), (1842, 4404201698619555840000), (1851, 54778388874854400000), (1854, -9280530725231001600000), (1855, 34864691456596377600000), (1857, 10563661873945313280000), (1867, -15111984861079142400000), (1868, -6403063116880281600000), (1869, 15111984861079142400000), (1871, 3201531558440140800000), (1873, 7417350658916352000000), (1874, 7685347844476108800000), (1880, 4097268088154357760000), (1881, -2900413559198711808000), (1882, -59568121389514752000), (1883, 414737902356922368000), (1884, 2451504521281536000000), (1885, 3659948525761855488000), (1886, -31848465594580992000), (1887, -4218827410224709632000), (1888, 2542985543602667520000), (1889, -95323232121126912000), (1890, 888215115745198080000), (1893, 1951341470849433600000), (1894, -4302905736953069568000), (1897, 3169748139186585600000), (1900, 2197036481036156928000), (1901, 3660221256271921152000), (1902, 1249731921884479488000), (1903, 328270556047343616000), (1904, -304877566989434880000), (1905, -2451504521281536000000), (1906, -2711614482074566656000), (1910, 2753869669962743808000), (1911, 2124806707563724800000), (1912, -2124806707563724800000), (1914, 665857147118026752000), (1915, -3210049119603916800000)]

def targetRow10 : Integer.Sparse (Fin 3237) := [(1916, -450757951040323584000), (1917, -423147689038577664000), (1921, 4172340565215019008000), (1922, -847409560407244800000), (1923, 2180351629537837056000), (1924, 3772583761333911552000), (1925, 669848715789926400000), (1927, -18738707098219315200000), (1928, 178978720009420800000), (1930, 2657205919166496768000), (1931, 189716558307655680000), (1932, -15347047775786237952000), (1933, -47964420247215144960000), (1934, -4714040967153057792000), (1935, 151499143634485248000), (1936, -21951447043276800000), (1938, -4207603471599403008000), (1939, 160580769836433408000), (1940, -5448613796115775488000), (1941, 1891520709844598784000), (1942, -3902216098532032512000), (1943, 6171454343172980736000), (1944, 3357311730124455936000), (1945, 4773540463463890944000), (1946, -189385081118392320000), (1947, 4201772064568049664000), (1948, -9128085858785230848000), (1949, -8100920986277511168000), (1950, 8923926439329398784000), (1951, -22996102308321558528000), (1952, -5202654127895347200000), (1953, 5202654127895347200000), (1954, -1346211378226003968000), (1955, -3407495751248117760000), (1957, 27983833967776038912000), (1958, -28257993540927553536000), (1959, -4946831880077574144000), (1962, -8092322011089469440000), (1963, -7444916811245813760000), (1964, -416428679821787136000), (1965, -1016042941450027008000), (1967, -21955095856769531904000), (1968, -14378100853333819392000), (1969, 12269398826405855232000), (1970, -22778979783065468928000), (1971, -1080639818309173248000), (1973, -7680684652994691072000), (1974, 4689897337119375360000), (1975, -4714450911702024192000), (1976, 1029413887898812416000), (1977, -218973289450438656000), (1978, -9759313319373176832000), (1979, -41624715574343172096000), (1980, -13085671563284447232000), (1981, -13743886838351265792000), (1983, 10817029381629542400000), (1984, -6752922376232632320000), (1986, -3995973679581757440000), (1987, -1340821167243264000000), (1988, 4806257162718412800000), (1989, 7655273626113146880000), (1991, 416003421044736000000), (1992, 9566869889386414080000), (1993, -1653558743737958400000)]

def targetRow11 : Integer.Sparse (Fin 3237) := [(1994, -2050187137963130880000), (1995, -3435263414499409920000), (1996, 7633541508433182720000), (1997, -590178927323381760000), (1998, -4479366205522575360000), (1999, 5011857085783080960000), (2000, 999901708930252800000), (2001, -7972461087479562240000), (2002, -5777870711254548480000), (2003, 8961285504761856000000), (2004, 1274912738715893760000), (2005, -2262212174315520000000), (2007, -11618393320164556800000), (2008, -10406241466564608000000), (2009, 6238836832370688000000), (2019, 2089015568665804800000), (2020, 5660818630174310400000), (2021, -5194848837860720640000), (2029, -3445367674768588800000), (2030, -3526248379837317120000), (2031, 1340821167243264000000), (2032, -21284105174522265600000), (2033, -6729430235975516160000), (2034, 3526248379837317120000), (2044, 9976743826758696960000), (2045, -416003421044736000000), (2046, -1781271279310602240000), (2047, 3469795674486865920000), (2048, -9976743826758696960000), (2050, 9212700734303109120000), (2051, -3934716707045376000000), (2052, 3435263414499409920000), (2054, 8305600448385515520000), (2055, 2724268260332666880000), (2056, 1355923199361024000000), (2057, 6564939594419404800000), (2058, -1057001205647278080000), (2059, -5105263763930480640000), (2060, 3946875325262069760000), (2061, -5660818630174310400000), (2062, -9762840630358179840000), (2063, 16607243005555507200000), (2064, 13705060285808640000000), (2074, -2757638739876249600000), (2080, -359649951169904640000), (2081, 19302033754623836160000), (2082, 6891745041155358720000), (2084, 20635690283060428800000), (2086, 6436794359666442240000), (2087, 829623023566848000000), (2088, -16476867997522329600000), (2089, -8398043666546688000000), (2095, 33959038618062028800000), (2096, -571357054756454400000), (2097, -8958732411045150720000), (2098, -39828535728449126400000), (2101, -12088519805730816000000), (2102, -15967457567244288000000), (2112, -421979070165811200000), (2114, 669848715789926400000), (2116, 15200456282416742400000), (2128, -4525925648641818624000), (2133, -5814069266409062400000), (2134, 1699294017721466880000)]

def targetRow12 : Integer.Sparse (Fin 3237) := [(2135, -3657804786659229696000), (2137, -12883500708986880000000), (2138, -4222719607976755200000), (2139, 4597326756229939200000), (2140, 2216831132152627200000), (2141, -4250125755517501440000), (2144, 3735836684119572480000), (2145, -12943331682486976512000), (2146, 14492549870804533248000), (2147, 9313996009718808576000), (2148, 919241958555648000000), (2151, -2589617639009157120000), (2152, -16300334708112752640000), (2153, 4564186441588408320000), (2154, 3365072991753338880000), (2156, -4404201698619555840000), (2157, 3906032471591878656000), (2158, 7967955760767959040000), (2159, -4205865767222181888000), (2160, -2674283432529494016000), (2161, 16753008632221532160000), (2162, -4052239562185113600000), (2164, 259351328607436800000), (2165, -1852188959337873408000), (2166, -4597326756229939200000), (2168, 7350751094580117504000), (2169, -5639933671031439360000), (2171, -8048462097973248000000), (2172, 1668709084299264000000), (2174, 4020809998518190080000), (2175, 15546685904170057728000), (2176, -1716666600863563776000), (2177, -15812369946008616960000), (2178, 18561918376033320960000), (2179, -12298111992747786240000), (2180, -1415934024744960000000), (2181, -50941984034146222080000), (2182, -22351245374360125440000), (2184, -3891082594516992000000), (2185, -10769461456860610560000), (2186, 23327342262493839360000), (2187, 34405213211462467584000), (2188, 12622627890148147200000), (2190, 6748651458342420480000), (2191, -2711226786498478080000), (2192, -814591422450892800000), (2193, -6439173843973570560000), (2194, -2879161744832593920000), (2195, -16011049661961338880000), (2196, 814591422450892800000), (2197, -616542244556636160000), (2198, 9470910448608215040000), (2200, 6932067331465543680000), (2201, 5023829814312960000000), (2202, 8259752936279900160000), (2211, 2995585454962114560000), (2212, -4348786044622602240000), (2214, -2995585454962114560000), (2217, 519512794327941120000), (2218, -6260504027114373120000), (2219, 10736042127096545280000), (2220, -9579839035999518720000), (2224, 6664563524103045120000), (2225, 9579839035999518720000)]

def targetRow13 : Integer.Sparse (Fin 3237) := [(2226, -10880841765483970560000), (2229, -8772590858152181760000), (2230, -8754560341097840640000), (2231, -1174798139719680000000), (2234, 6466249688175083520000), (2235, 1899117244195799040000), (2236, 419312052798750720000), (2237, 6894774206306058240000), (2238, 11475455859405619200000), (2240, -12951213345010483200000), (2241, -12438782405973245952000), (2265, 1331003266183987200000), (2267, 5933039869919232000000), (2268, -1531997227471011840000), (2269, 9156607353476481024000), (2270, 1182595905074626560000), (2271, 270860476671590400000), (2272, 1979586319187312640000), (2276, 3863114615263002624000), (2277, 53914691091824640000), (2278, -2204937138861047808000), (2281, -2066297949707894784000), (2282, -992147345927700480000), (2298, 305084947161415680000), (2299, 2654462499211837440000), (2300, 1619043489526579200000), (2301, -1521451825330913280000), (2304, -8946502007384309760000), (2305, -3789395265230733312000), (2306, -9536788940949946368000), (2307, -1889903966198169600000), (2308, 752859079780663296000), (2312, -1389583379072286720000), (2313, -565455270900989952000), (2316, -186994987012915200000), (2349, 4501291376384409600000), (2355, 654308882759024640000), (2356, -4735033992735621120000), (2358, 4935862034835701760000), (2359, -379671498467573760000), (2360, 2452540759969628160000), (2367, 28541892592926720000), (2369, -2426340427298242560000), (2370, -3915341740423249920000), (2371, -57083785185853440000), (2373, 6542432374534963200000), (2374, 16453451164259450880000), (2375, 10440815232685178880000), (2376, -684291540819640320000), (2383, 652996879610019840000), (2384, 3344441963460820992000), (2385, -1985415998552211456000), (2389, -2989726119329660928000), (2390, 355417517501448192000), (2391, -1559990074286407680000), (2394, -354715844131160064000), (2395, 814999240525381632000), (2421, 744619799330684928000), (2422, 4783674936826920960000), (2424, 5808432531870646272000), (2428, 23220776228880384000), (2431, 2229127337632333824000), (2432, -2370794412740640768000), (2433, -3066113985645182976000)]

def targetRow14 : Integer.Sparse (Fin 3237) := [(2434, 3058373744961454080000), (2435, -722635406229897216000), (2436, -3632663000341315584000), (2440, 506711554922151936000), (2442, -1835451633733337088000), (2443, -4633408883520700416000), (2444, 1856913308405858304000), (2448, -4726817018446086144000), (2453, -416003421044736000000), (2456, 4958849630270914560000), (2458, -8093713655448207360000), (2459, -416003421044736000000), (2467, 7799955337720627200000), (2468, -3146577964923617280000), (2470, -1421726643557498880000), (2471, 7390298065975050240000), (2472, -1331003266183987200000), (2473, -270860476671590400000), (2474, -3141806478252244992000), (2476, 1646462429022781440000), (2477, 3031883170345451520000), (2479, -500927005576101888000), (2482, -12294580299389337600000), (2483, -1072771597873446912000), (2484, -8846701964077694976000), (2487, 2431584286271078400000), (2488, 6558674437762449408000), (2489, 2212486243651289088000), (2490, 3690491308938362880000), (2491, 16118436415397363712000), (2492, 4491472530225364992000), (2494, 7698731041103413248000), (2495, 1252704393088598016000), (2496, 6590198986965909504000), (2497, 442881254805405696000), (2498, -2683554743866687488000), (2499, -1438088403369590784000), (2500, -3946797413223727104000), (2501, -1069653250219180032000), (2503, -3159921714170167296000), (2504, 1255758373127946240000), (2508, -1133832859511095296000), (2509, -5933039869919232000000), (2510, -5743947411554107392000), (2511, -1645301575619444736000), (2512, 900394580334477312000), (2513, 8704054146298871808000), (2517, 2987270009704415232000), (2520, 5653339486845861888000), (2524, 1962225745433985024000), (2525, 2433073703307706368000), (2526, 12926463385317801984000), (2527, -16798163909915049984000), (2528, 19725678159807578112000), (2532, 4629005356695552000000), (2533, 13978224602687471616000), (2534, 4549640633792593920000), (2535, 831414264535056384000), (2536, 9247678918847889408000), (2537, 6894463966772723712000), (2538, -24789990154844307456000), (2539, 29008204646800490496000), (2567, -8568495025249517568000), (2570, 13643436319594905600000)]

def targetRow15 : Integer.Sparse (Fin 3237) := [(2571, -6320730118534594560000), (2573, 4205984660170997760000), (2574, 8841142471881129984000), (2575, 7417776676181114880000), (2578, -3609060248797839360000), (2579, 17665403553650442240000), (2589, -3558260895488409600000), (2590, 2856821572837048320000), (2591, 8029997437000089600000), (2592, -2089015568665804800000), (2593, -3375760173907968000000), (2595, 2139241300593868800000), (2602, -669848715789926400000), (2606, 5058598529834680320000), (2607, -2714220736148275200000), (2609, -5214891424162775040000), (2610, -1773350590788403200000), (2611, -5315776700851814400000), (2615, 3611345102733312000000), (2616, 3293229788164915200000), (2620, -6378432071205519360000), (2621, 8915230341595791360000), (2622, -10603132867144581120000), (2623, 23153419811192832000000), (2624, 7818430382751744000000), (2625, 3622287461825249280000), (2629, 11249654248211742720000), (2633, 7397988905631744000000), (2634, 6831804330736680960000), (2635, 12949195045327994880000), (2636, -26217469888567050240000), (2637, 3090408338022727680000), (2638, -12931866039110860800000), (2641, 498588466060984320000), (2642, -4479366205522575360000), (2643, -15823981309321543680000), (2644, 1301788622079590400000), (2655, 885060905467576320000), (2659, -2229127337632333824000), (2660, 7779502517921906688000), (2661, -2581778767834054656000), (2662, -3482485535088967680000), (2663, 722635406229897216000), (2666, -629877478875660288000), (2670, -1457354951397015552000), (2674, -23279727428871782400000), (2675, 4493455024472064000000), (2676, 1745085365617950720000), (2677, -4452974806184755200000), (2678, 1278536233166438400000), (2681, 5625894605263994880000), (2682, -16392111811529932800000), (2683, 2738043209843343360000), (2684, 1441864010724802560000), (2693, 28561312752775004160000), (2694, -5754636709648662528000), (2695, -5516271414691430400000), (2696, -6944207726412988416000), (2698, 7171430266513981440000), (2699, -41044357386388242432000), (2702, 17523027587499098112000), (2703, -44429797684470546432000), (2704, -14940765337926500352000), (2706, 2089015568665804800000)]

def targetRow16 : Integer.Sparse (Fin 3237) := [(2708, -8130580131269836800000), (2709, -27260971487782502400000), (2711, 7114320400788357120000), (2712, 68789051986378752000), (2713, 6338956605336649728000), (2714, 1889903966198169600000), (2716, -4570457455456026624000), (2717, 13539206030830534656000), (2718, 12880096071349764096000), (2719, 31561229726387601408000), (2720, -20356532239770058752000), (2721, 1438088403369590784000), (2722, 2124827740548366336000), (2723, -42494557453973323776000), (2724, -12145658229120761856000), (2725, -9902480791530700800000), (2726, 23117333999818899456000), (2727, 605854592861995008000), (2728, -911950238443732992000), (2729, -586664655103328256000), (2732, 3337175163583070208000), (2734, 3405889229126565888000), (2735, -590135600217784320000), (2736, -2103251398787137536000), (2737, 11553704265979330560000), (2738, -5908225161862840320000), (2739, -7328462957249495040000), (2740, -3964459607742283776000), (2741, 12077999364458151936000), (2742, -13261355412674052096000), (2743, 6667737054748213248000), (2746, 14474271087478702080000), (2747, 312413012981121024000), (2748, 22823498120703049728000), (2749, 14943427389004972032000), (2750, -2586375627759157248000), (2760, 20807680974515011584000), (2762, -31265001811798917120000), (2763, 5315776700851814400000), (2764, -30197898181904302080000), (2765, -6895433910022963200000), (2766, 20494784666407403520000), (2767, -4788850420540440576000), (2768, 13884969959188070400000), (2769, 34895135196929064960000), (2770, 3526248379837317120000), (2775, -30372260691522355200000), (2776, -5798712689427087360000), (2778, -7800059930768179200000), (2780, 11604214120782495744000), (2781, -3649006690387623936000), (2782, 1801181590773497856000), (2783, -28415965546457137152000), (2784, -22837858583598858240000), (2785, 6539548315307212800000), (2786, -3287644928768212992000), (2787, -33534778140264038400000), (2788, -11253260405800304640000), (2789, 8806052365250789376000), (2790, 3649006690387623936000), (2791, 31534403806896979968000), (2792, -19036929296722821120000), (2793, -2288930879160188928000), (2794, -41423402361966428160000)]

def targetRow17 : Integer.Sparse (Fin 3237) := [(2795, 12266190676214415360000), (2796, 7296061782863314944000), (2797, -5386149831850131456000), (2802, -8408006041455820800000), (2803, -3803939670426255360000), (2831, 40954261856247742464000), (2832, 57085031128334598144000), (2833, 2514535969799798784000), (2839, 71116174175593365504000), (2840, 82312803291315437568000), (2841, -4224921028263936000000), (2842, -7805365883397734400000), (2843, 4224921028263936000000), (2844, -8843655738973224960000), (2845, 1116328705839857664000), (2846, -11450522454042083328000), (2847, 7805365883397734400000), (2848, 6128597253147328512000), (2849, -462947814736920576000), (2850, 5593363103425757184000), (2851, 2053490911783944192000), (2852, 7912784430110343168000), (2853, 14905306338389655552000), (2854, -761589926485032960000), (2855, 368168093238951936000), (2856, -5693122080040550400000), (2858, 5693122080040550400000), (2859, -7248938720166936576000), (2860, 12502505035448451072000), (2861, 3231726734524022784000), (2862, -716116926716706816000), (2863, 12949757789032415232000), (2864, 1197078318949072896000), (2865, -97261095987707904000), (2866, -2940208664430772224000), (2867, -4362670631726088192000), (2868, -2461303460148019200000), (2869, 2418118564976787456000), (2870, 11195660614200459264000), (2871, 5221252535535009792000), (2872, 16817110373118246912000), (2873, 14664773306621362176000), (2874, 3643443110785056768000), (2875, -4407922008608735232000), (2876, 1765372925391667200000), (2878, 3157621618243534848000), (2879, 17560644030085201920000), (2880, 3552084349459365888000), (2881, -483156672380928000000), (2882, 2200392789160624128000), (2883, 8030508152059330560000), (2884, 2333580197392023552000), (2885, -19011338932645527552000), (2886, -6166085797247975424000), (2887, -19274765724083552256000), (2888, 5544829063963607040000), (2889, 6870049258648633344000), (2890, 476851978047062016000), (2891, -382460818968281088000), (2892, 9211036774796623872000), (2893, 17575348253457383424000), (2894, -34507362327330816000), (2910, -13515513231445327872000), (2911, -19241651017431908352000)]

def targetRow18 : Integer.Sparse (Fin 3237) := [(2913, -2216492015908552704000), (2915, 9836938992486187008000), (2916, -2888188832156221440000), (2920, -24911231228112273408000), (2922, -11076753145762676736000), (2926, -3609473985785364480000), (2927, -8041495388340879360000), (2928, -8553475027189628928000), (2929, 15007094450225676288000), (2930, -14254645456457957376000), (2931, 18099022219727339520000), (2932, -1896689902925905920000), (2936, -4276208522593566720000), (2937, 7704059375140208640000), (2940, -4470330666478731264000), (2941, 5324013064735948800000), (2942, 4730383620298506240000), (2943, -6127988909884047360000), (2944, 1083441906686361600000), (2945, 7918345276749250560000), (2946, -4345332613952569344000), (2947, 215658764367298560000), (2948, -8819748555444191232000), (2949, -3968589383710801920000), (2950, -14113916079842525184000), (2951, 8499226830254899200000), (2952, 23732159479676928000000), (2953, 36626429413905924096000), (2954, 15452458461052010496000), (2955, 14639794103047421952000), (2956, -11692002548014645248000), (2957, -8265191798831579136000), (2958, -1142729568214843392000), (2959, 1220339788645662720000), (2960, 6476173958106316800000), (2961, -6085807301323653120000), (2962, -15157581060922933248000), (2963, -7559615864792678400000), (2964, 3011436319122653184000), (2965, 10617849996847349760000), (2966, -1692590756154310656000), (2967, -35786008029537239040000), (2968, -38147155763799785472000), (2969, -5558333516289146880000), (2970, -10846457928298266624000), (2971, -2261821083603959808000), (2972, -757540324473569280000), (2973, -747979948051660800000), (2974, -875893157801754624000), (2975, -4224921028263936000000), (2976, -5601048967764246528000), (2977, 4938879732374568960000), (2978, -7805365883397734400000), (2979, 1400988782872756224000), (2980, 1662907014489047040000), (2981, -799209977907511296000), (2982, -16331923481962217472000), (2983, 1843237901377732608000), (2985, -5693122080040550400000), (2986, 2989735781018370048000), (2987, -20337198821419253760000), (2988, -4166088676073275392000), (2989, 4331084313932070912000), (2990, -7832344641172144128000)]

def targetRow19 : Integer.Sparse (Fin 3237) := [(2991, 419207923271467008000), (2992, 2088377879151771648000), (2993, 4668687916798574592000), (2994, -47757709229948928000), (2995, -11360929018687782912000), (2996, -12243947554527510528000), (2997, -9017233195750391808000), (2998, 1426161328576266240000), (2999, 323950101685862400000), (3000, 2481540634666598400000), (3001, 6123206211439951872000), (3002, 5611114966542188544000), (3003, -4157338039461347328000), (3004, -9921532838029295616000), (3005, -9955508355996844032000), (3006, -3552860462980792320000), (3007, 1531209998492762112000), (3008, -10577125298707365888000), (3009, -2142501973049475072000), (3010, -7032198870020653056000), (3011, 2026857879932239872000), (3012, -2118434941245063168000), (3013, 12472080070696501248000), (3014, 13670070453059715072000), (3015, 1819985088072646656000), (3020, -3874325650567593984000), (3021, 2175984329530540032000), (3023, -657568140574851072000), (3026, 9126733393928650752000), (3028, 6795525312677412864000), (3031, 10203027601367236608000), (3032, 16684169003853152256000), (3033, -4302249789556260864000), (3034, -9689775870270504960000), (3035, 24425621100813090816000), (3039, 4276208522593566720000), (3040, 14865336275325419520000), (3043, -10611725918904778752000), (3047, -3651536391380140032000), (3048, 25540881314177875968000), (3049, -8931969569439350784000), (3052, 47721697208593809408000), (3054, 3301651066537377792000), (3055, 25180426029650411520000), (3057, -1313798019878486016000), (3058, 21125648675937189888000), (3059, 58246227271801110528000), (3060, 15911341251193995264000), (3061, 9824764650698833920000), (3062, 19178062513867063296000), (3063, -1093534813718839296000), (3064, 22163666956793413632000), (3065, 39451307385118261248000), (3066, 6273766636234997760000), (3067, -1647434443064868864000), (3068, -7941663994208845824000), (3069, 2611987518440079360000), (3070, 1421670070005792768000), (3071, -6239960297145630720000), (3072, 3259996962101526528000), (3073, 13377767853843283968000), (3074, -11958904477318643712000), (3075, -127393862378323968000), (3076, -1418863376524640256000)]

def targetRow20 : Integer.Sparse (Fin 3237) := [(3077, 19134699747307683840000), (3078, -5686906574229995520000), (3079, -5324013064735948800000), (3080, 29561192263900200960000), (3081, -1083441906686361600000), (3082, -12567225913008979968000), (3083, -4535331438044381184000), (3084, -23732159479676928000000), (3085, -18533635534082801664000), (3086, -22975789646216429568000), (3087, -8499226830254899200000), (3088, -16875309640898838528000), (3095, 2978479197322739712000), (3096, 16389072352617431040000), (3097, 23233730127482585088000), (3098, 92883104915521536000), (3099, -9483177650962563072000), (3100, -2890541624919588864000), (3101, -7341806534933348352000), (3103, -14530652001365262336000), (3105, 7427653233623433216000), (3108, -12264455942580731904000), (3112, 8916509350529335296000), (3113, 12233494979845816320000), (3114, 2026846219688607744000), (3115, -18907268073784344576000), (3118, 1037405314429747200000), (3119, 6797176070885867520000), (3120, -6581206302477778944000), (3121, 1658951609427689472000), (3122, -2003708022304407552000), (3123, 6585849716091125760000), (3125, 12127532681381806080000), (3126, -49178321197557350400000), (3127, -17211622947812278272000), (3128, 3601578321337909248000), (3129, 11949080038817660928000), (3131, 26234697751049797632000), (3132, -1803031804161294336000), (3133, -1219510267957739520000), (3134, 34816216585195487232000), (3135, 758866233230622720000), (3136, 22613357947383447552000), (3137, 13429246920497823744000), (3138, -4064171765800108032000), (3141, -4291086391493787648000), (3142, 9726337145084313600000), (3143, 30794924164413652992000), (3144, 5010817572354392064000), (3145, -5752353613478363136000), (3146, 7848902981735940096000), (3147, 9732294813230825472000), (3148, 55912898410749886464000), (3149, 18198562535170375680000), (3150, 16689362260860076032000), (3151, 11015478679850975232000), (3152, -11601654236794847232000), (3153, -238272485558059008000), (3154, 9806018085126144000000), (3155, 10171942174410670080000), (3156, -381292928484507648000), (3157, 3552860462980792320000), (3159, 7805365883397734400000), (3160, 12678992556746342400000)]

def targetRow21 : Integer.Sparse (Fin 3237) := [(3162, 8788145924144627712000), (3163, 14640885025087684608000), (3164, 4998927687537917952000), (3165, 1313082224189374464000), (3166, -9806018085126144000000), (3167, 2663428588472107008000), (3168, -12840196478415667200000), (3169, 8721406518151348224000), (3170, 20804483957839626240000), (3171, -15787189652894908416000), (3173, -18103702594567274496000), (3174, 10628823676665987072000), (3175, 9126071378630148096000), (3177, -16830413886397612032000), (3178, 642323079345733632000), (3179, -25288345262529183744000), (3180, -23758552131121446912000), (3181, -28266402523973419008000), (3182, -30906556284937568256000), (3183, 19094161853855563776000), (3184, 23882407552008585216000), (3185, -48308943425120501760000), (3186, -7408755837351493632000), (3187, -5384845512904015872000), (3188, -13629983004992471040000), (3189, 68956627891077513216000), (3190, -12260480058351157248000), (3191, -23256277065636249600000), (3192, -14631219146636918784000), (3193, -1665714719287148544000), (3194, -190845340189813112832000), (3195, -90385457830414516224000), (3196, -4322559273236692992000), (3197, -9865202604365316096000), (3198, -19050929198037467136000), (3199, 4117655551595249664000), (3200, -18048588276902658048000), (3201, 3540243621870305280000), (3202, 31118010071687626752000), (3203, 2890541624919588864000), (3204, -2519509915502641152000), (3206, -10327115071336218624000), (3209, -8916509350529335296000), (3210, -13929942140355870720000), (3211, -5829419805588062208000), (3213, 275156207945515008000), (3214, 7559615864792678400000), (3215, 28457281603153428480000), (3216, 25355826421346598912000), (3217, 13348700654332280832000), (3218, 13623556916506263552000), (3220, -22065085658765721600000), (3221, -37595573886288789504000), (3222, -2360542400871137280000), (3223, 5752353613478363136000), (3224, -8413005595148550144000), (3225, -29313851828997980160000), (3226, -31786630521973899264000), (3227, 9684849239753490432000), (3228, -9244716940057116672000), (3229, 16445950118093389824000), (3230, 88096283133573464064000), (3231, -2629572249391202304000), (3232, -164858414417055055872000)]

def targetRow22 : Integer.Sparse (Fin 3237) := [(3233, 14596026761550495744000), (3234, 26158193261228851200000), (3235, -14596026761550495744000), (3236, -62042723667542016000000)]

def targetRow24 : Integer.Sparse (Fin 3237) := [(980, -17592701091840000), (983, -936841682681856000), (985, 25270131769344000), (988, -43284967391232000), (989, -66287913172992000), (990, -100442434240512000), (994, -556741643673600000), (995, -416691553001472000), (997, -1605719865286656000), (998, 237445782110208000), (1000, 962615842578432000), (1001, 529909890048000000), (1003, -7252787920896000), (1006, -65970371690496000), (1007, -25084272181248000), (1008, -15151695003648000), (1011, 370312876265472000), (1012, -1839498808283136000), (1013, 1595974778044416000), (1014, -1509566498463744000), (1015, 5476838105088000), (1107, -144978003394560000), (1111, -79758594736128000), (1112, -24482297806848000), (1113, -404490410311680000), (1114, 8575281476665344000), (1115, -1557495071096832000), (1131, -4691279229493248000), (1143, -2851874417000448000), (1145, 965685661065216000), (1147, -60125200515072000), (1150, -247635703332864000), (1151, -17454999453696000), (1152, -100755460915200000), (1156, 4809718816358400000), (1161, -7279375122432000), (1165, -1474410567942144000), (1166, -82183798996992000), (1167, 193696709197824000), (1168, -124103037026304000), (1169, -83298204057600000), (1172, -260014553874432000), (1173, -72019461685248000), (1174, 55848172584960000), (1176, 3034948619501568000), (1180, -36612833918976000), (1231, -1701394035425280000), (1354, -555321360384000000), (1468, -5769581253230592000), (1527, 330372566286336000), (1528, 43921555292160000), (1551, 1539851453005824000), (1555, 286873897992192000), (1558, -114016956383232000), (1561, 335903205851136000), (1563, -95388859367424000), (1565, 68227775594496000), (1573, 848783867904000), (1576, 76860088123392000), (1577, 4064318779981824000), (1593, 451203370942464000), (1595, -242575607070720000), (1603, 1135349755674624000), (1612, 108671423938560000)]

def targetRow25 : Integer.Sparse (Fin 3237) := [(1614, -51550075551744000), (1617, -12984211021824000), (1622, -511379530260480000), (1626, -273694672355328000), (1627, 63839382405120000), (1630, -694313355681792000), (1632, 151289704710144000), (1651, -7051332180049920000), (1744, -890530790768640000), (1753, 3223479468883968000), (1758, 26456900169498624000), (1769, -1642848265175040000), (1784, 87608340578304000), (1786, -465983095947264000), (1787, 685387956879360000), (1857, -2006335441797120000), (1890, -502163260784640000), (1896, 1651357549191168000), (1915, 456617879617536000), (1922, 60558622064640000), (1925, -3416811063902208000), (1928, 142547531857920000), (1932, 31360948244914176000), (1933, -19586194789883904000), (1934, -4074229660999680000), (1935, -8242881260027904000), (1939, -515156125188096000), (1951, 3689448017117184000), (1999, 5133953501429760000), (2009, -3527329044234240000), (2087, -449962300440576000), (2097, 12801969801363456000), (2128, 9035635359744000), (2160, -2703064156950528000), (2182, -1824147897384960000), (2266, -926668817399808000), (2270, -79388380495872000), (2274, 6410216679358464000), (2277, 105637473091584000), (2280, 986536172224512000), (2283, 2098436517789696000), (2285, 4000425031766016000), (2286, -1325137101152256000), (2298, -356481699840000000), (2300, -810364358393856000), (2305, -220823764697088000), (2315, -3780660052205568000), (2317, 5953779642875904000), (2318, -2267800314974208000), (2319, 680347801018368000), (2320, -1173267870695424000), (2321, -247116667650048000), (2322, 2378173048086528000), (2387, 4242979507027968000), (2390, 139968071663616000), (2419, 8042288474529792000), (2425, 2616002296233984000), (2427, 343881623715840000), (2434, -254454568058880000), (2437, 8031968501760000), (2447, 7223424237969408000), (2448, 55912884830208000), (2449, 6277088792346624000), (2475, 1037438749089792000)]

def targetRow26 : Integer.Sparse (Fin 3237) := [(2489, 2878611234250752000), (2490, 16950414249345024000), (2495, 153170874630144000), (2543, -1194996261150720000), (2546, -212929623244800000), (2553, -10751315877421056000), (2554, -3468666704154624000), (2555, -4327348598415360000), (2556, -12719334145351680000), (2557, 9745892295177830400), (2558, -12185711788413542400), (2561, 743643274493952000), (2565, 16559265177623347200), (2574, -13493195843678208000), (2578, -20210086361493504000), (2704, -4187375384887296000), (2751, -4710232141848576000), (2752, -879889012531200000), (2763, -61688676577812480000), (2764, -55446900981792768000), (2766, 2064795054465024000), (2799, 6542321247557222400), (2801, 214816141957939200), (2802, 12016838264868864000), (2806, 550285919988940800), (2807, -190320669691084800), (2808, 177432975227289600), (2809, 105770634839654400), (2812, 1169707994903347200), (2814, 465274368942243840), (2816, -4047752421788221440), (2817, -2937325054426398720), (2818, 1309444989924556800), (2819, -391458704765829120), (2828, -6301786333615718400), (2829, 7228708133881651200), (2832, -7376582402858188800), (2840, -24855286642308218880), (2842, -57789539942400000), (2843, 830812926246912000), (2844, -41030573359104000), (2845, 675102221402112000), (2846, 427482069073920000), (2847, -660823389241344000), (2849, -80760882069504000), (2850, 640368299999232000), (2851, -433144641355776000), (2852, 206579546062848000), (2853, -1131525211815936000), (2854, -75162520387584000), (2855, -136959203082240000), (2856, -462440727576576000), (2857, -313508254187520000), (2858, -436202671177728000), (2859, -114688157810688000), (2860, -595193133072384000), (2861, -277967687122944000), (2862, -325030043713536000), (2863, -224963843457024000), (2864, -472099406413824000), (2865, -131928703893504000), (2866, 1807710987091968000), (2867, 312601279463424000), (2868, 1126095402958848000)]

def targetRow27 : Integer.Sparse (Fin 3237) := [(2873, -1401125455134720000), (2880, -1063372683018240000), (2884, 927176984100864000), (2886, -890398356406272000), (2887, 212613335875584000), (2889, -765305071534080000), (2890, -574861448577024000), (2892, -40536954372096000), (2893, -1924743835090944000), (2894, -333192816230400000), (2910, -1125655961665536000), (2913, -1191481859506176000), (2915, -586250803740672000), (2916, -555866147192832000), (2920, -1177489968463872000), (2922, -1450589689479168000), (2926, 28282762690560000), (2927, 691180956942336000), (2928, 733698407006208000), (2930, 53912824971264000), (2931, 137310354800640000), (2932, -122960289005568000), (2937, 370737957961728000), (2940, -28031940034560000), (2942, 1235702897049600000), (2944, -161521764139008000), (2946, 121213560029184000), (2947, 317469245571072000), (2949, 1330513861017600000), (2952, -594275122151424000), (2953, -519636319469568000), (2954, -1201378318221312000), (2956, -213640705474560000), (2957, -105080646795264000), (2959, 5269852226322432000), (2960, 7878761007022080000), (2961, 1810510167932928000), (2962, 104599067295744000), (2965, 2128533229928448000), (2966, -2339483109949440000), (2967, -4719719885045760000), (2968, 871008761806848000), (2970, -185841528864768000), (2981, -220756042579968000), (2982, 13725015736320000), (2991, 39224650235904000), (3001, -257741348143104000), (3002, 262220037488640000), (3003, -339946968711168000), (3004, -49012753563648000), (3009, -208042343792640000), (3014, -289308884336640000), (3015, 209414845366272000), (3020, -288520297906176000), (3026, 652552261337088000), (3028, -200951085662208000), (3033, 1456669630660608000), (3039, 120473131548672000), (3040, 245713900142592000), (3049, -2433312855687168000), (3057, -23723810095104000), (3058, -3635925221376000), (3060, 1539007685591040000), (3061, 1521442073346048000)]

def targetRow28 : Integer.Sparse (Fin 3237) := [(3063, 781236323352576000), (3064, 275541730394112000), (3065, 1441146718126080000), (3066, 472272975691776000), (3067, -73284360339456000), (3068, 2566072284217344000), (3070, -978280595324928000), (3071, -1247965115056128000), (3074, 567035781709824000), (3075, 755598234746880000), (3076, -642041788760064000), (3078, 58584146116608000), (3086, 199097004589056000), (3105, -911052097191936000), (3108, -2971875249487872000), (3113, 974548354203648000), (3115, 830941347446784000), (3119, 2865177298206720000), (3120, -127570409422848000), (3123, -36407410163712000), (3126, -1174752991641600000), (3131, -3525559239573504000), (3133, -1213315470065664000), (3142, 11073752038637568000), (3143, 4377870677311488000), (3144, -744449669332992000), (3147, -5043269071798272000), (3150, -3315403965726720000), (3151, -1650878603329536000), (3157, 189260743311360000), (3167, 759697680236544000), (3168, 1672700174401536000), (3170, -14120815894069248000), (3171, -17267698136973312000), (3173, 2356292241063936000), (3175, -39922458930708480000), (3178, 351360402849792000), (3179, -2629406008147968000), (3180, -17025027217293312000), (3184, 504326104547328000), (3185, -2188351423512576000), (3186, -317571581214720000), (3189, -23558399576506368000), (3190, -58850816751304704000), (3192, 1762336165330944000), (3195, 12739463290552320000), (3196, -174849476788224000), (3206, -276787817349120000), (3221, 283307199823872000)]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def familyAverage (B : Fin 7 → Basis) (F : CMatrix → ℝ) : ℝ :=
  average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate0 : ExponentCode := ⟨0, 0, ![]⟩

def coordinate1 : ExponentCode := ⟨2, 2, ![![-2, 2], ![2, -2]]⟩

def coordinate2 : ExponentCode := ⟨2, 2, ![![-3, 3], ![3, -3]]⟩

def coordinate3 : ExponentCode := ⟨3, 3, ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]⟩

def coordinate4 : ExponentCode := ⟨3, 3, ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate5 : ExponentCode := ⟨3, 2, ![![-4, 4], ![2, -2], ![2, -2]]⟩

def coordinate6 : ExponentCode := ⟨2, 2, ![![-4, 4], ![4, -4]]⟩

def coordinate7 : ExponentCode := ⟨3, 3, ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]⟩

def coordinate8 : ExponentCode := ⟨3, 3, ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate9 : ExponentCode := ⟨3, 2, ![![-5, 5], ![2, -2], ![3, -3]]⟩

def coordinate10 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]⟩

def coordinate11 : ExponentCode := ⟨3, 3, ![![-2, 1, 1], ![1, -4, 3], ![1, 3, -4]]⟩

def coordinate12 : ExponentCode := ⟨3, 3, ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]⟩

def coordinate13 : ExponentCode := ⟨3, 3, ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]⟩

def coordinate14 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate15 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate16 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinate17 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate18 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate19 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate20 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate21 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate22 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate23 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]⟩

def coordinate24 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate25 : ExponentCode := ⟨4, 3, ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]⟩

def coordinate26 : ExponentCode := ⟨3, 3, ![![-2, 1, 1], ![1, -3, 2], ![1, 2, -3]]⟩

def coordinate27 : ExponentCode := ⟨4, 2, ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]⟩

def coordinate28 : ExponentCode := ⟨4, 4, ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate29 : ExponentCode := ⟨4, 4, ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate30 : ExponentCode := ⟨4, 3, ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate31 : ExponentCode := ⟨4, 3, ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate32 : ExponentCode := ⟨3, 3, ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]⟩

def coordinate33 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]⟩

def coordinate34 : ExponentCode := ⟨3, 3, ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]⟩

def coordinate35 : ExponentCode := ⟨3, 3, ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]⟩

def coordinate36 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate37 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate38 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinate39 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate40 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate41 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate42 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate43 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]⟩

def coordinate44 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate45 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate46 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate47 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate48 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate49 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate50 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 0, -1]]⟩

def coordinate51 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate52 : ExponentCode := ⟨3, 3, ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]⟩

def coordinate53 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 1, -3]]⟩

def coordinate54 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]⟩

def coordinate55 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]⟩

def coordinate56 : ExponentCode := ⟨4, 3, ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate57 : ExponentCode := ⟨4, 4, ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate58 : ExponentCode := ⟨2, 2, ![![-5, 5], ![5, -5]]⟩

def coordinate59 : ExponentCode := ⟨4, 3, ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]⟩

def coordinate60 : ExponentCode := ⟨3, 3, ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]⟩

def coordinate61 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]⟩

def coordinate62 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]⟩

def coordinate63 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]⟩

def coordinateChunk0 : Array ExponentCode := #[coordinate0, coordinate1, coordinate2, coordinate3, coordinate4, coordinate5, coordinate6, coordinate7, coordinate8, coordinate9, coordinate10, coordinate11, coordinate12, coordinate13, coordinate14, coordinate15, coordinate16, coordinate17, coordinate18, coordinate19, coordinate20, coordinate21, coordinate22, coordinate23, coordinate24, coordinate25, coordinate26, coordinate27, coordinate28, coordinate29, coordinate30, coordinate31, coordinate32, coordinate33, coordinate34, coordinate35, coordinate36, coordinate37, coordinate38, coordinate39, coordinate40, coordinate41, coordinate42, coordinate43, coordinate44, coordinate45, coordinate46, coordinate47, coordinate48, coordinate49, coordinate50, coordinate51, coordinate52, coordinate53, coordinate54, coordinate55, coordinate56, coordinate57, coordinate58, coordinate59, coordinate60, coordinate61, coordinate62, coordinate63]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate64 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]⟩

def coordinate65 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]⟩

def coordinate66 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate67 : ExponentCode := ⟨3, 3, ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]⟩

def coordinate68 : ExponentCode := ⟨4, 2, ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]⟩

def coordinate69 : ExponentCode := ⟨3, 3, ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]⟩

def coordinate70 : ExponentCode := ⟨3, 3, ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]⟩

def coordinate71 : ExponentCode := ⟨3, 3, ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate72 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate73 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate74 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate75 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate76 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate77 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate78 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate79 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]⟩

def coordinate80 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate81 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]⟩

def coordinate82 : ExponentCode := ⟨3, 3, ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]⟩

def coordinate83 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate84 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate85 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate86 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate87 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]⟩

def coordinate88 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -3, 0]]⟩

def coordinate89 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, 0, -3]]⟩

def coordinate90 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -3, 0]]⟩

def coordinate91 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate92 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -2, 0]]⟩

def coordinate93 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate94 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]⟩

def coordinate95 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -1, -2]]⟩

def coordinate96 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, -1, 0]]⟩

def coordinate97 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]⟩

def coordinate98 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]⟩

def coordinate99 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]⟩

def coordinate100 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]⟩

def coordinate101 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]⟩

def coordinate102 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate103 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]⟩

def coordinate104 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]⟩

def coordinate105 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]⟩

def coordinate106 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 2, -1, -2]]⟩

def coordinate107 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate108 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, 1, -1, -2]]⟩

def coordinate109 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![2, 0, 0, -2]]⟩

def coordinate110 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -3, 1]]⟩

def coordinate111 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 2, -1, -2]]⟩

def coordinate112 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 0, -2]]⟩

def coordinate113 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, 1, -2]]⟩

def coordinate114 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]⟩

def coordinate115 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]⟩

def coordinate116 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, -1, 0]]⟩

def coordinate117 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate118 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 1, 0, -2]]⟩

def coordinate119 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]⟩

def coordinate120 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate121 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]⟩

def coordinate122 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]⟩

def coordinate123 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]⟩

def coordinate124 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]⟩

def coordinate125 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]⟩

def coordinate126 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate127 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]⟩

def coordinateChunk1 : Array ExponentCode := #[coordinate64, coordinate65, coordinate66, coordinate67, coordinate68, coordinate69, coordinate70, coordinate71, coordinate72, coordinate73, coordinate74, coordinate75, coordinate76, coordinate77, coordinate78, coordinate79, coordinate80, coordinate81, coordinate82, coordinate83, coordinate84, coordinate85, coordinate86, coordinate87, coordinate88, coordinate89, coordinate90, coordinate91, coordinate92, coordinate93, coordinate94, coordinate95, coordinate96, coordinate97, coordinate98, coordinate99, coordinate100, coordinate101, coordinate102, coordinate103, coordinate104, coordinate105, coordinate106, coordinate107, coordinate108, coordinate109, coordinate110, coordinate111, coordinate112, coordinate113, coordinate114, coordinate115, coordinate116, coordinate117, coordinate118, coordinate119, coordinate120, coordinate121, coordinate122, coordinate123, coordinate124, coordinate125, coordinate126, coordinate127]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate640 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]⟩

def coordinate641 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![2, -2, 1, -1]]⟩

def coordinate642 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]⟩

def coordinate643 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]⟩

def coordinate644 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinate645 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate646 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -3, 2]]⟩

def coordinate647 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 2, -1, -1], ![1, -1, -2, 2], ![1, -1, 3, -3]]⟩

def coordinate648 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![0, 1, 1, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate649 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate650 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate651 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate652 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, -3, 1, 2], ![1, 1, 1, -3], ![1, 2, -3, 0]]⟩

def coordinate653 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 2, -1, -2]]⟩

def coordinate654 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 2, -2, -1]]⟩

def coordinate655 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 2, -3, 0]]⟩

def coordinate656 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 3, -3, 0], ![2, -1, 0, -1]]⟩

def coordinate657 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 3, -2, -1], ![2, -1, -1, 0]]⟩

def coordinate658 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 2, -3, 0]]⟩

def coordinate659 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate660 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]⟩

def coordinate661 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 0, 2], ![0, 3, -3, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate662 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate663 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -3, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate664 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 2, 1, -3], ![2, -1, -1, 0]]⟩

def coordinate665 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 2, -1, -2]]⟩

def coordinate666 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate667 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate668 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 3, -2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate669 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 2, 0], ![0, 0, -3, 3], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate670 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate671 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]⟩

def coordinate672 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate673 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate674 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate675 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![1, 1, 1, -3]]⟩

def coordinate676 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]⟩

def coordinate677 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]⟩

def coordinate678 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]⟩

def coordinate679 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]⟩

def coordinate680 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]⟩

def coordinate681 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 2, -2, -1]]⟩

def coordinate682 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate683 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 1, 1, -3]]⟩

def coordinate684 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 1, 0, -2]]⟩

def coordinate685 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]⟩

def coordinate686 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]⟩

def coordinate687 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate688 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 3, -2, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate689 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 3, -2, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate690 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]⟩

def coordinate691 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate692 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -2, -1, 1]]⟩

def coordinate693 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]⟩

def coordinate694 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -3, 2, 0], ![1, 1, 0, -2]]⟩

def coordinate695 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -3, 2, 0], ![1, 1, -1, -1]]⟩

def coordinate696 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 3, -1, -2], ![1, -2, 1, 0], ![1, -1, 1, -1]]⟩

def coordinate697 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 0, -2]]⟩

def coordinate698 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 0, -2]]⟩

def coordinate699 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate700 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, -1, 1, -1]]⟩

def coordinate701 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -3, 2, 0], ![1, 2, 0, -3]]⟩

def coordinate702 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]⟩

def coordinate703 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -3, 1, 1], ![1, 1, -1, -1]]⟩

def coordinateChunk10 : Array ExponentCode := #[coordinate640, coordinate641, coordinate642, coordinate643, coordinate644, coordinate645, coordinate646, coordinate647, coordinate648, coordinate649, coordinate650, coordinate651, coordinate652, coordinate653, coordinate654, coordinate655, coordinate656, coordinate657, coordinate658, coordinate659, coordinate660, coordinate661, coordinate662, coordinate663, coordinate664, coordinate665, coordinate666, coordinate667, coordinate668, coordinate669, coordinate670, coordinate671, coordinate672, coordinate673, coordinate674, coordinate675, coordinate676, coordinate677, coordinate678, coordinate679, coordinate680, coordinate681, coordinate682, coordinate683, coordinate684, coordinate685, coordinate686, coordinate687, coordinate688, coordinate689, coordinate690, coordinate691, coordinate692, coordinate693, coordinate694, coordinate695, coordinate696, coordinate697, coordinate698, coordinate699, coordinate700, coordinate701, coordinate702, coordinate703]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate704 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 0, 1, -2]]⟩

def coordinate705 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, -3, 1, 1], ![1, 0, 1, -2]]⟩

def coordinate706 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, -1, 2, -2]]⟩

def coordinate707 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, -1, -1, 1]]⟩

def coordinate708 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, -1, -1, 1]]⟩

def coordinate709 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]⟩

def coordinate710 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 0, -2, 1]]⟩

def coordinate711 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -3, 2]]⟩

def coordinate712 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, -1, 1]]⟩

def coordinate713 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3], ![1, 1, -1, -1]]⟩

def coordinate714 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 2, -3, 1], ![1, -3, 1, 1], ![1, 1, 1, -3]]⟩

def coordinate715 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 3, -3, 0], ![1, -3, 0, 2], ![1, 0, 2, -3]]⟩

def coordinate716 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 3, -2, -1], ![1, -2, -1, 2], ![1, -1, 2, -2]]⟩

def coordinate717 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]⟩

def coordinate718 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, 2, -1], ![0, 2, -2], ![1, -3, 2], ![2, -1, -1]]⟩

def coordinate719 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]⟩

def coordinate720 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate721 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]⟩

def coordinate722 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![0, -3, 3], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]⟩

def coordinate723 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]⟩

def coordinate724 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]⟩

def coordinate725 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate726 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]⟩

def coordinate727 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]⟩

def coordinate728 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]⟩

def coordinate729 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate730 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate731 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 1, 0, -2]]⟩

def coordinate732 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, 0, -2]]⟩

def coordinate733 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 1, 0, -2]]⟩

def coordinate734 : ExponentCode := ⟨5, 4, ![![-2, 0, 3, -1], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate735 : ExponentCode := ⟨4, 4, ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate736 : ExponentCode := ⟨4, 4, ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate737 : ExponentCode := ⟨4, 4, ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]⟩

def coordinate738 : ExponentCode := ⟨4, 4, ![![-2, 1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinate739 : ExponentCode := ⟨4, 4, ![![-2, 1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate740 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate741 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate742 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate743 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]⟩

def coordinate744 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate745 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 1, -3]]⟩

def coordinate746 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, 0, -2]]⟩

def coordinate747 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]⟩

def coordinate748 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate749 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate750 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate751 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]⟩

def coordinate752 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, -2, 1, -1]]⟩

def coordinate753 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![1, -2, 2, -1], ![1, 1, 1, -3]]⟩

def coordinate754 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate755 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -2, 1]]⟩

def coordinate756 : ExponentCode := ⟨5, 4, ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]⟩

def coordinate757 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![1, -2, -1, 2], ![1, 1, -1, -1]]⟩

def coordinate758 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, 2, -2]]⟩

def coordinate759 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2], ![1, -1, 1, -1]]⟩

def coordinate760 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]⟩

def coordinate761 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate762 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate763 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate764 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![2, -1, -1, 0]]⟩

def coordinate765 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![1, -1, 3, -3], ![1, 1, -1, -1]]⟩

def coordinate766 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 1, -3]]⟩

def coordinate767 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinateChunk11 : Array ExponentCode := #[coordinate704, coordinate705, coordinate706, coordinate707, coordinate708, coordinate709, coordinate710, coordinate711, coordinate712, coordinate713, coordinate714, coordinate715, coordinate716, coordinate717, coordinate718, coordinate719, coordinate720, coordinate721, coordinate722, coordinate723, coordinate724, coordinate725, coordinate726, coordinate727, coordinate728, coordinate729, coordinate730, coordinate731, coordinate732, coordinate733, coordinate734, coordinate735, coordinate736, coordinate737, coordinate738, coordinate739, coordinate740, coordinate741, coordinate742, coordinate743, coordinate744, coordinate745, coordinate746, coordinate747, coordinate748, coordinate749, coordinate750, coordinate751, coordinate752, coordinate753, coordinate754, coordinate755, coordinate756, coordinate757, coordinate758, coordinate759, coordinate760, coordinate761, coordinate762, coordinate763, coordinate764, coordinate765, coordinate766, coordinate767]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate768 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -1, -2, 1]]⟩

def coordinate769 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![2, -1, 0, -1]]⟩

def coordinate770 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate771 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate772 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate773 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]⟩

def coordinate774 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate775 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -3, 3], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate776 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate777 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate778 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, 0, 0]]⟩

def coordinate779 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate780 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate781 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate782 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 2, -3], ![2, -2, 1, -1]]⟩

def coordinate783 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![2, -2, 0, 0]]⟩

def coordinate784 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 1, 0], ![1, 1, 2, -4]]⟩

def coordinate785 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 2, -1], ![1, 1, 1, -3]]⟩

def coordinate786 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![1, -2, 3, -2], ![1, 1, 0, -2]]⟩

def coordinate787 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -1, 1]]⟩

def coordinate788 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -1, -1]]⟩

def coordinate789 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinate790 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate791 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate792 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, -1, -1, 1]]⟩

def coordinate793 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -1, -3, 3], ![1, -1, 1, -1]]⟩

def coordinate794 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, -1, 1]]⟩

def coordinate795 : ExponentCode := ⟨5, 3, ![![-2, 1, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]⟩

def coordinate796 : ExponentCode := ⟨4, 3, ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate797 : ExponentCode := ⟨5, 3, ![![-2, 1, 1], ![0, -2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate798 : ExponentCode := ⟨4, 4, ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![1, -1, 1, -1], ![1, 1, 1, -3]]⟩

def coordinate799 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate800 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate801 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 1, -1, -1]]⟩

def coordinate802 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]⟩

def coordinate803 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]⟩

def coordinate804 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, 1, 0, -2]]⟩

def coordinate805 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 0, 1, -2]]⟩

def coordinate806 : ExponentCode := ⟨4, 4, ![![-2, 1, 2, -1], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate807 : ExponentCode := ⟨5, 4, ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate808 : ExponentCode := ⟨5, 4, ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate809 : ExponentCode := ⟨4, 4, ![![-2, 1, 2, -1], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 1, -3]]⟩

def coordinate810 : ExponentCode := ⟨4, 4, ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate811 : ExponentCode := ⟨4, 4, ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![1, -1, -2, 2], ![1, 1, 0, -2]]⟩

def coordinate812 : ExponentCode := ⟨4, 4, ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate813 : ExponentCode := ⟨4, 4, ![![-2, 2, -1, 1], ![0, -1, -2, 3], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate814 : ExponentCode := ⟨4, 4, ![![-2, 2, -1, 1], ![0, -1, -2, 3], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate815 : ExponentCode := ⟨5, 4, ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate816 : ExponentCode := ⟨5, 4, ![![-2, 2, 0, 0], ![0, -1, -2, 3], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate817 : ExponentCode := ⟨5, 4, ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate818 : ExponentCode := ⟨4, 3, ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate819 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, -1, 2, 0], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate820 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate821 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate822 : ExponentCode := ⟨4, 4, ![![-1, -2, 0, 3], ![-1, -1, 3, -1], ![1, 1, -1, -1], ![1, 2, -2, -1]]⟩

def coordinate823 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate824 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate825 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate826 : ExponentCode := ⟨4, 4, ![![-1, -2, 0, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 2, -3, 0]]⟩

def coordinate827 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate828 : ExponentCode := ⟨5, 4, ![![-1, -2, 0, 3], ![-1, 2, -1, 0], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate829 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate830 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate831 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinateChunk12 : Array ExponentCode := #[coordinate768, coordinate769, coordinate770, coordinate771, coordinate772, coordinate773, coordinate774, coordinate775, coordinate776, coordinate777, coordinate778, coordinate779, coordinate780, coordinate781, coordinate782, coordinate783, coordinate784, coordinate785, coordinate786, coordinate787, coordinate788, coordinate789, coordinate790, coordinate791, coordinate792, coordinate793, coordinate794, coordinate795, coordinate796, coordinate797, coordinate798, coordinate799, coordinate800, coordinate801, coordinate802, coordinate803, coordinate804, coordinate805, coordinate806, coordinate807, coordinate808, coordinate809, coordinate810, coordinate811, coordinate812, coordinate813, coordinate814, coordinate815, coordinate816, coordinate817, coordinate818, coordinate819, coordinate820, coordinate821, coordinate822, coordinate823, coordinate824, coordinate825, coordinate826, coordinate827, coordinate828, coordinate829, coordinate830, coordinate831]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate832 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 2, 0], ![0, 1, -2, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate833 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate834 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate835 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate836 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate837 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate838 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, -1, 1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate839 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, -1, 1], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate840 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate841 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, -1, 1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate842 : ExponentCode := ⟨4, 4, ![![-1, -2, 1, 2], ![-1, 1, -1, 1], ![1, -1, 2, -2], ![1, 2, -2, -1]]⟩

def coordinate843 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate844 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate845 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, 1, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate846 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 1, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate847 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate848 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, -1, 0], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate849 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, -1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate850 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate851 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, 0, -1], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate852 : ExponentCode := ⟨5, 4, ![![-1, -2, 1, 2], ![-1, 2, 0, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate853 : ExponentCode := ⟨4, 4, ![![-1, -2, 1, 2], ![-1, 2, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]⟩

def coordinate854 : ExponentCode := ⟨5, 3, ![![-1, -2, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate855 : ExponentCode := ⟨4, 4, ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate856 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 0, 2], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate857 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate858 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate859 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate860 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate861 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate862 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate863 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, -1, 2, 0], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate864 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate865 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate866 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate867 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate868 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate869 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate870 : ExponentCode := ⟨4, 4, ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]⟩

def coordinate871 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, -2, 2, 0], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate872 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate873 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate874 : ExponentCode := ⟨5, 4, ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate875 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 0, 2], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate876 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![1, 1, -3, 1], ![1, 1, 0, -2]]⟩

def coordinate877 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, -1, -1]]⟩

def coordinate878 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -3, 1]]⟩

def coordinate879 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 3, -3, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate880 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 2, 0], ![0, 1, -3, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate881 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 2, 0], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate882 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 2, 0], ![0, 3, -2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate883 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate884 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]⟩

def coordinate885 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate886 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate887 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]⟩

def coordinate888 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 2, -3, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate889 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 3, -3, 0], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate890 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 3, -2, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate891 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate892 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, -2, 3, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate893 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate894 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate895 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinateChunk13 : Array ExponentCode := #[coordinate832, coordinate833, coordinate834, coordinate835, coordinate836, coordinate837, coordinate838, coordinate839, coordinate840, coordinate841, coordinate842, coordinate843, coordinate844, coordinate845, coordinate846, coordinate847, coordinate848, coordinate849, coordinate850, coordinate851, coordinate852, coordinate853, coordinate854, coordinate855, coordinate856, coordinate857, coordinate858, coordinate859, coordinate860, coordinate861, coordinate862, coordinate863, coordinate864, coordinate865, coordinate866, coordinate867, coordinate868, coordinate869, coordinate870, coordinate871, coordinate872, coordinate873, coordinate874, coordinate875, coordinate876, coordinate877, coordinate878, coordinate879, coordinate880, coordinate881, coordinate882, coordinate883, coordinate884, coordinate885, coordinate886, coordinate887, coordinate888, coordinate889, coordinate890, coordinate891, coordinate892, coordinate893, coordinate894, coordinate895]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate896 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -2, 1]]⟩

def coordinate897 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate898 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate899 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate900 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate901 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate902 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, 0, -2, 3], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate903 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate904 : ExponentCode := ⟨5, 3, ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate905 : ExponentCode := ⟨5, 4, ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate906 : ExponentCode := ⟨5, 4, ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate907 : ExponentCode := ⟨5, 4, ![![-1, 0, -1, 2], ![-1, 1, -2, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate908 : ExponentCode := ⟨5, 4, ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinateChunk14 : Array ExponentCode := #[coordinate896, coordinate897, coordinate898, coordinate899, coordinate900, coordinate901, coordinate902, coordinate903, coordinate904, coordinate905, coordinate906, coordinate907, coordinate908]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate128 : ExponentCode := ⟨3, 3, ![![-2, -1, 3], ![0, 4, -4], ![2, -3, 1]]⟩

def coordinate129 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, -2, 0], ![2, 0, 1, -3]]⟩

def coordinate130 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -2, 0]]⟩

def coordinate131 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]⟩

def coordinate132 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 3, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate133 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 3, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate134 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 3, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinate135 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 3, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate136 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 3, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate137 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]⟩

def coordinate138 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]⟩

def coordinate139 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate140 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]⟩

def coordinate141 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -2, 0, 0]]⟩

def coordinate142 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -2, 0]]⟩

def coordinate143 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate144 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate145 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]⟩

def coordinate146 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate147 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate148 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate149 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate150 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate151 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]⟩

def coordinate152 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate153 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate154 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -2, 0]]⟩

def coordinate155 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate156 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate157 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate158 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate159 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 1, -2]]⟩

def coordinate160 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]⟩

def coordinate161 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate162 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate163 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate164 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate165 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate166 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate167 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate168 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate169 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate170 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate171 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]⟩

def coordinate172 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate173 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate174 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]⟩

def coordinate175 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 0, -2, 1]]⟩

def coordinate176 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]⟩

def coordinate177 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]⟩

def coordinate178 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]⟩

def coordinate179 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate180 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![1, 1, -3, 1], ![1, 1, 1, -3]]⟩

def coordinate181 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate182 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate183 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate184 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate185 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate186 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]⟩

def coordinate187 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate188 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate189 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![2, -2, 0, 0]]⟩

def coordinate190 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]⟩

def coordinate191 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 1, 0, -2]]⟩

def coordinateChunk2 : Array ExponentCode := #[coordinate128, coordinate129, coordinate130, coordinate131, coordinate132, coordinate133, coordinate134, coordinate135, coordinate136, coordinate137, coordinate138, coordinate139, coordinate140, coordinate141, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate152, coordinate153, coordinate154, coordinate155, coordinate156, coordinate157, coordinate158, coordinate159, coordinate160, coordinate161, coordinate162, coordinate163, coordinate164, coordinate165, coordinate166, coordinate167, coordinate168, coordinate169, coordinate170, coordinate171, coordinate172, coordinate173, coordinate174, coordinate175, coordinate176, coordinate177, coordinate178, coordinate179, coordinate180, coordinate181, coordinate182, coordinate183, coordinate184, coordinate185, coordinate186, coordinate187, coordinate188, coordinate189, coordinate190, coordinate191]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate192 : ExponentCode := ⟨5, 4, ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate193 : ExponentCode := ⟨4, 4, ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]⟩

def coordinate194 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]⟩

def coordinate195 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]⟩

def coordinate196 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]⟩

def coordinate197 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate198 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]⟩

def coordinate199 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]⟩

def coordinate200 : ExponentCode := ⟨5, 3, ![![-2, 0, 2], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1]]⟩

def coordinate201 : ExponentCode := ⟨4, 3, ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]⟩

def coordinate202 : ExponentCode := ⟨5, 4, ![![-2, 0, 2, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate203 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![2, -1, 1, -2]]⟩

def coordinate204 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate205 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]⟩

def coordinate206 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate207 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]⟩

def coordinate208 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate209 : ExponentCode := ⟨4, 4, ![![-2, 1, -1, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]⟩

def coordinate210 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate211 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate212 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate213 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate214 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate215 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]⟩

def coordinate216 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]⟩

def coordinate217 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]⟩

def coordinate218 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate219 : ExponentCode := ⟨5, 4, ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate220 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -3, 2], ![2, -2, 0, 0]]⟩

def coordinate221 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![1, -2, 0, 1], ![1, 1, -3, 1]]⟩

def coordinate222 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate223 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate224 : ExponentCode := ⟨4, 4, ![![-2, 1, 0, 1], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -3, 2]]⟩

def coordinate225 : ExponentCode := ⟨5, 3, ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]⟩

def coordinate226 : ExponentCode := ⟨4, 3, ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]⟩

def coordinate227 : ExponentCode := ⟨5, 3, ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate228 : ExponentCode := ⟨4, 3, ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]⟩

def coordinate229 : ExponentCode := ⟨5, 4, ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate230 : ExponentCode := ⟨4, 4, ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![2, -2, 1, -1]]⟩

def coordinate231 : ExponentCode := ⟨4, 4, ![![-2, 2, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, -1, -1, 1]]⟩

def coordinate232 : ExponentCode := ⟨5, 4, ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, -2, 1], ![1, 0, 1, -2]]⟩

def coordinate233 : ExponentCode := ⟨5, 4, ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate234 : ExponentCode := ⟨4, 4, ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![0, 0, 3, -3], ![2, -2, 0, 0]]⟩

def coordinate235 : ExponentCode := ⟨5, 4, ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate236 : ExponentCode := ⟨4, 3, ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate237 : ExponentCode := ⟨4, 3, ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]⟩

def coordinate238 : ExponentCode := ⟨4, 3, ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate239 : ExponentCode := ⟨4, 4, ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate240 : ExponentCode := ⟨4, 4, ![![-1, -1, -1, 3], ![-1, -1, 3, -1], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate241 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 1, 1], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate242 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, -1, 2, 0], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate243 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate244 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate245 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate246 : ExponentCode := ⟨5, 4, ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate247 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate248 : ExponentCode := ⟨4, 4, ![![-1, -1, 1, 1], ![-1, 1, -2, 2], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate249 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate250 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate251 : ExponentCode := ⟨5, 4, ![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate252 : ExponentCode := ⟨5, 4, ![![-1, 0, -1, 2], ![-1, 1, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate253 : ExponentCode := ⟨4, 4, ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate254 : ExponentCode := ⟨4, 4, ![![-1, 1, -2, 2], ![-1, 1, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinate255 : ExponentCode := ⟨5, 4, ![![-1, 1, -1, 1], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinateChunk3 : Array ExponentCode := #[coordinate192, coordinate193, coordinate194, coordinate195, coordinate196, coordinate197, coordinate198, coordinate199, coordinate200, coordinate201, coordinate202, coordinate203, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate215, coordinate216, coordinate217, coordinate218, coordinate219, coordinate220, coordinate221, coordinate222, coordinate223, coordinate224, coordinate225, coordinate226, coordinate227, coordinate228, coordinate229, coordinate230, coordinate231, coordinate232, coordinate233, coordinate234, coordinate235, coordinate236, coordinate237, coordinate238, coordinate239, coordinate240, coordinate241, coordinate242, coordinate243, coordinate244, coordinate245, coordinate246, coordinate247, coordinate248, coordinate249, coordinate250, coordinate251, coordinate252, coordinate253, coordinate254, coordinate255]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate256 : ExponentCode := ⟨4, 3, ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]⟩

def coordinate257 : ExponentCode := ⟨3, 3, ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]⟩

def coordinate258 : ExponentCode := ⟨4, 3, ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]⟩

def coordinate259 : ExponentCode := ⟨4, 3, ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]⟩

def coordinate260 : ExponentCode := ⟨4, 3, ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]⟩

def coordinate261 : ExponentCode := ⟨3, 3, ![![-3, -1, 4], ![0, 4, -4], ![3, -3, 0]]⟩

def coordinate262 : ExponentCode := ⟨4, 3, ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate263 : ExponentCode := ⟨5, 3, ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]⟩

def coordinate264 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]⟩

def coordinate265 : ExponentCode := ⟨5, 3, ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]⟩

def coordinate266 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]⟩

def coordinate267 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![0, 4, -4], ![1, -2, 1], ![2, -2, 0]]⟩

def coordinate268 : ExponentCode := ⟨4, 3, ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]⟩

def coordinate269 : ExponentCode := ⟨5, 3, ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]⟩

def coordinate270 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, -2, 2], ![0, 3, -3], ![3, -2, -1]]⟩

def coordinate271 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]⟩

def coordinate272 : ExponentCode := ⟨5, 3, ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate273 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]⟩

def coordinate274 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![0, 3, -3], ![1, -3, 2], ![2, -1, -1]]⟩

def coordinate275 : ExponentCode := ⟨4, 3, ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]⟩

def coordinate276 : ExponentCode := ⟨3, 3, ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]⟩

def coordinate277 : ExponentCode := ⟨4, 3, ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]⟩

def coordinate278 : ExponentCode := ⟨3, 3, ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]⟩

def coordinate279 : ExponentCode := ⟨4, 4, ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate280 : ExponentCode := ⟨4, 4, ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate281 : ExponentCode := ⟨4, 4, ![![-2, -2, -1, 5], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate282 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]⟩

def coordinate283 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, 1, -3, 0]]⟩

def coordinate284 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate285 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate286 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]⟩

def coordinate287 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]⟩

def coordinate288 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]⟩

def coordinate289 : ExponentCode := ⟨4, 4, ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]⟩

def coordinate290 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]⟩

def coordinate291 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]⟩

def coordinate292 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 1, -3]]⟩

def coordinate293 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]⟩

def coordinate294 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, 0, 0, -2]]⟩

def coordinate295 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![1, 1, -3, 1], ![1, 1, 0, -2]]⟩

def coordinate296 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, -1, -1]]⟩

def coordinate297 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, -1, -1]]⟩

def coordinate298 : ExponentCode := ⟨4, 4, ![![-2, -2, 1, 3], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -3, 1]]⟩

def coordinate299 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, -1, -2]]⟩

def coordinate300 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 1, -3]]⟩

def coordinate301 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate302 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate303 : ExponentCode := ⟨4, 4, ![![-2, -2, 2, 2], ![0, 1, -3, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate304 : ExponentCode := ⟨4, 4, ![![-2, -2, 3, 1], ![0, 0, -3, 3], ![0, 2, 0, -2], ![2, 0, 0, -2]]⟩

def coordinate305 : ExponentCode := ⟨4, 4, ![![-2, -2, 3, 1], ![0, 0, -3, 3], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate306 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]⟩

def coordinate307 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]⟩

def coordinate308 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]⟩

def coordinate309 : ExponentCode := ⟨4, 3, ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]⟩

def coordinate310 : ExponentCode := ⟨3, 3, ![![-2, -2, 4], ![1, -2, 1], ![1, 4, -5]]⟩

def coordinate311 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]⟩

def coordinate312 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]⟩

def coordinate313 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -2, 0]]⟩

def coordinate314 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 0, 1, -2], ![1, 2, -2, -1]]⟩

def coordinate315 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]⟩

def coordinate316 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate317 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate318 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinate319 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinateChunk4 : Array ExponentCode := #[coordinate256, coordinate257, coordinate258, coordinate259, coordinate260, coordinate261, coordinate262, coordinate263, coordinate264, coordinate265, coordinate266, coordinate267, coordinate268, coordinate269, coordinate270, coordinate271, coordinate272, coordinate273, coordinate274, coordinate275, coordinate276, coordinate277, coordinate278, coordinate279, coordinate280, coordinate281, coordinate282, coordinate283, coordinate284, coordinate285, coordinate286, coordinate287, coordinate288, coordinate289, coordinate290, coordinate291, coordinate292, coordinate293, coordinate294, coordinate295, coordinate296, coordinate297, coordinate298, coordinate299, coordinate300, coordinate301, coordinate302, coordinate303, coordinate304, coordinate305, coordinate306, coordinate307, coordinate308, coordinate309, coordinate310, coordinate311, coordinate312, coordinate313, coordinate314, coordinate315, coordinate316, coordinate317, coordinate318, coordinate319]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate320 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate321 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]⟩

def coordinate322 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 2, 0, -3]]⟩

def coordinate323 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]⟩

def coordinate324 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate325 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate326 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]⟩

def coordinate327 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate328 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate329 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate330 : ExponentCode := ⟨4, 4, ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate331 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate332 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![0, 2, -1, -1], ![2, 0, -2, 0]]⟩

def coordinate333 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate334 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate335 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate336 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 1, -3, 0]]⟩

def coordinate337 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![0, 3, -3, 0], ![2, 0, 1, -3]]⟩

def coordinate338 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 2, 0], ![1, 1, 1, -3], ![1, 2, -3, 0]]⟩

def coordinate339 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![0, 2, -2, 0], ![2, 1, -1, -2]]⟩

def coordinate340 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![0, 2, -1, -1], ![2, 1, -2, -1]]⟩

def coordinate341 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![0, 3, -3, 0], ![2, 0, 0, -2]]⟩

def coordinate342 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![0, 3, -2, -1], ![2, 0, -1, -1]]⟩

def coordinate343 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![0, 3, -1, -2], ![2, 0, -2, 0]]⟩

def coordinate344 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![1, 1, -2, 0], ![1, 2, -1, -2]]⟩

def coordinate345 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![1, 1, -1, -1], ![1, 2, -2, -1]]⟩

def coordinate346 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -2, 3, -1], ![1, 1, 0, -2], ![1, 2, -3, 0]]⟩

def coordinate347 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate348 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate349 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate350 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -1, -1]]⟩

def coordinate351 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate352 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 1, -1, -2]]⟩

def coordinate353 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]⟩

def coordinate354 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 2, -1, -2]]⟩

def coordinate355 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]⟩

def coordinate356 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate357 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, -1, -1]]⟩

def coordinate358 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate359 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![0, 2, -2, 0], ![2, -1, -1, 0]]⟩

def coordinate360 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate361 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -3, 1], ![2, 0, 1, -3]]⟩

def coordinate362 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate363 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate364 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -2, 1], ![1, 0, 1, -2]]⟩

def coordinate365 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, 0, -3, 1]]⟩

def coordinate366 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -3, 1], ![1, 1, 1, -3]]⟩

def coordinate367 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, 1, -1, -2]]⟩

def coordinate368 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 2, -3, 1], ![2, 0, 0, -2]]⟩

def coordinate369 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, 0, -3, 1]]⟩

def coordinate370 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 3, -3, 0], ![2, -1, 0, -1]]⟩

def coordinate371 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![0, 3, -2, -1], ![2, -1, -1, 0]]⟩

def coordinate372 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![1, 0, -2, 1], ![1, 2, -1, -2]]⟩

def coordinate373 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, -1, 3, -2], ![1, 1, -3, 1], ![1, 1, 0, -2]]⟩

def coordinate374 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, 0, -1]]⟩

def coordinate375 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, 0, -1]]⟩

def coordinate376 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate377 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate378 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, -1, 1, -2]]⟩

def coordinate379 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, 0, -3]]⟩

def coordinate380 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate381 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate382 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate383 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]⟩

def coordinateChunk5 : Array ExponentCode := #[coordinate320, coordinate321, coordinate322, coordinate323, coordinate324, coordinate325, coordinate326, coordinate327, coordinate328, coordinate329, coordinate330, coordinate331, coordinate332, coordinate333, coordinate334, coordinate335, coordinate336, coordinate337, coordinate338, coordinate339, coordinate340, coordinate341, coordinate342, coordinate343, coordinate344, coordinate345, coordinate346, coordinate347, coordinate348, coordinate349, coordinate350, coordinate351, coordinate352, coordinate353, coordinate354, coordinate355, coordinate356, coordinate357, coordinate358, coordinate359, coordinate360, coordinate361, coordinate362, coordinate363, coordinate364, coordinate365, coordinate366, coordinate367, coordinate368, coordinate369, coordinate370, coordinate371, coordinate372, coordinate373, coordinate374, coordinate375, coordinate376, coordinate377, coordinate378, coordinate379, coordinate380, coordinate381, coordinate382, coordinate383]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate384 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate385 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate386 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]⟩

def coordinate387 : ExponentCode := ⟨5, 4, ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate388 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 3, -3], ![0, 2, -3, 1], ![2, -1, 0, -1]]⟩

def coordinate389 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -2, 1]]⟩

def coordinate390 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 3, -3], ![0, 3, -3, 0], ![2, -2, 0, 0]]⟩

def coordinate391 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 2, -2, -1]]⟩

def coordinate392 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]⟩

def coordinate393 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 1, -1, -1]]⟩

def coordinate394 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 2, -3, 0]]⟩

def coordinate395 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 1, 1, -3]]⟩

def coordinate396 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -3, 1]]⟩

def coordinate397 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 2, -3, 0]]⟩

def coordinate398 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]⟩

def coordinate399 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate400 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate401 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 2, -3, 1], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate402 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]⟩

def coordinate403 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 3, -3, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate404 : ExponentCode := ⟨4, 4, ![![-2, -1, 0, 3], ![0, 3, -3, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate405 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate406 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![0, 2, -1, -1], ![2, 0, -2, 0]]⟩

def coordinate407 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate408 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate409 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate410 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -2, 1, 1], ![1, 1, 1, -3], ![1, 2, -3, 0]]⟩

def coordinate411 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 1, -2, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate412 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 1, -2, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate413 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 1, -2, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate414 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate415 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate416 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate417 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate418 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinate419 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate420 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate421 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]⟩

def coordinate422 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate423 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![2, 1, -2, -1]]⟩

def coordinate424 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]⟩

def coordinate425 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![2, 0, 2, -4]]⟩

def coordinate426 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![2, 0, -2, 0]]⟩

def coordinate427 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 2, -2, -1]]⟩

def coordinate428 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![1, 1, -2, 0], ![1, 1, 2, -4]]⟩

def coordinate429 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate430 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate431 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate432 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 2, -1, -1], ![2, -1, 0, -1]]⟩

def coordinate433 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 2, 0, -2], ![2, -1, -1, 0]]⟩

def coordinate434 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate435 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate436 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate437 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, -1, 2, -1], ![0, 3, -1, -2], ![2, -1, -2, 1]]⟩

def coordinate438 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]⟩

def coordinate439 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -1, 0]]⟩

def coordinate440 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, -1, -1, 0]]⟩

def coordinate441 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]⟩

def coordinate442 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]⟩

def coordinate443 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -1, 2, -3]]⟩

def coordinate444 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![1, -1, 2, -2], ![1, 2, -1, -2]]⟩

def coordinate445 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![2, -2, 0, 0]]⟩

def coordinate446 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate447 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 0, 1], ![1, 1, -1, -1]]⟩

def coordinateChunk6 : Array ExponentCode := #[coordinate384, coordinate385, coordinate386, coordinate387, coordinate388, coordinate389, coordinate390, coordinate391, coordinate392, coordinate393, coordinate394, coordinate395, coordinate396, coordinate397, coordinate398, coordinate399, coordinate400, coordinate401, coordinate402, coordinate403, coordinate404, coordinate405, coordinate406, coordinate407, coordinate408, coordinate409, coordinate410, coordinate411, coordinate412, coordinate413, coordinate414, coordinate415, coordinate416, coordinate417, coordinate418, coordinate419, coordinate420, coordinate421, coordinate422, coordinate423, coordinate424, coordinate425, coordinate426, coordinate427, coordinate428, coordinate429, coordinate430, coordinate431, coordinate432, coordinate433, coordinate434, coordinate435, coordinate436, coordinate437, coordinate438, coordinate439, coordinate440, coordinate441, coordinate442, coordinate443, coordinate444, coordinate445, coordinate446, coordinate447]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate448 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 1, -2, 0]]⟩

def coordinate449 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]⟩

def coordinate450 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 3, -2, -1], ![2, -2, -1, 1]]⟩

def coordinate451 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -1, 1, -2]]⟩

def coordinate452 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![2, -1, 0, -1]]⟩

def coordinate453 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]⟩

def coordinate454 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -3, 2], ![1, -1, 2, -2], ![1, 1, 0, -2]]⟩

def coordinate455 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate456 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate457 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate458 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate459 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 2, -1, -2]]⟩

def coordinate460 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]⟩

def coordinate461 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -2, 1]]⟩

def coordinate462 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate463 : ExponentCode := ⟨5, 4, ![![-2, -1, 1, 2], ![0, 1, 1, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]⟩

def coordinate464 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![0, 2, -3, 1], ![2, -2, 0, 0]]⟩

def coordinate465 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -2, 0, 1], ![1, 2, -3, 0]]⟩

def coordinate466 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2], ![1, 1, -1, -1]]⟩

def coordinate467 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]⟩

def coordinate468 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 1, 0, -2]]⟩

def coordinate469 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, -1, -1], ![1, -1, -2, 2], ![1, 0, 2, -3]]⟩

def coordinate470 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -3, 2]]⟩

def coordinate471 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -2, 1, 0], ![1, 1, -3, 1]]⟩

def coordinate472 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]⟩

def coordinate473 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 3, -2, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]⟩

def coordinate474 : ExponentCode := ⟨4, 4, ![![-2, -1, 1, 2], ![0, 3, -1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]⟩

def coordinate475 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![2, 0, 1, -3]]⟩

def coordinate476 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![2, 0, -1, -1]]⟩

def coordinate477 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, -1, -2, 3], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate478 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate479 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate480 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate481 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 1, -2]]⟩

def coordinate482 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, 0, -3, 3], ![0, 2, 0, -2], ![2, -1, 1, -2]]⟩

def coordinate483 : ExponentCode := ⟨4, 4, ![![-2, -1, 2, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![2, -1, 0, -1]]⟩

def coordinate484 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate485 : ExponentCode := ⟨5, 4, ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate486 : ExponentCode := ⟨5, 3, ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]⟩

def coordinate487 : ExponentCode := ⟨5, 3, ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]⟩

def coordinate488 : ExponentCode := ⟨5, 3, ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]⟩

def coordinate489 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]⟩

def coordinate490 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]⟩

def coordinate491 : ExponentCode := ⟨5, 3, ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]⟩

def coordinate492 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]⟩

def coordinate493 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]⟩

def coordinate494 : ExponentCode := ⟨4, 3, ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]⟩

def coordinate495 : ExponentCode := ⟨3, 3, ![![-2, -1, 3], ![1, -3, 2], ![1, 4, -5]]⟩

def coordinate496 : ExponentCode := ⟨5, 4, ![![-2, -1, 3, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 0, -2]]⟩

def coordinate497 : ExponentCode := ⟨5, 4, ![![-2, -1, 3, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, 1, 0, -2], ![1, 1, 0, -2]]⟩

def coordinate498 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![2, 0, 1, -3]]⟩

def coordinate499 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![2, 0, -1, -1]]⟩

def coordinate500 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate501 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]⟩

def coordinate502 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]⟩

def coordinate503 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]⟩

def coordinate504 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, -1, -1, 0]]⟩

def coordinate505 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]⟩

def coordinate506 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate507 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate508 : ExponentCode := ⟨4, 4, ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate509 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]⟩

def coordinate510 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate511 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]⟩

def coordinateChunk7 : Array ExponentCode := #[coordinate448, coordinate449, coordinate450, coordinate451, coordinate452, coordinate453, coordinate454, coordinate455, coordinate456, coordinate457, coordinate458, coordinate459, coordinate460, coordinate461, coordinate462, coordinate463, coordinate464, coordinate465, coordinate466, coordinate467, coordinate468, coordinate469, coordinate470, coordinate471, coordinate472, coordinate473, coordinate474, coordinate475, coordinate476, coordinate477, coordinate478, coordinate479, coordinate480, coordinate481, coordinate482, coordinate483, coordinate484, coordinate485, coordinate486, coordinate487, coordinate488, coordinate489, coordinate490, coordinate491, coordinate492, coordinate493, coordinate494, coordinate495, coordinate496, coordinate497, coordinate498, coordinate499, coordinate500, coordinate501, coordinate502, coordinate503, coordinate504, coordinate505, coordinate506, coordinate507, coordinate508, coordinate509, coordinate510, coordinate511]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate512 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate513 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate514 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]⟩

def coordinate515 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate516 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]⟩

def coordinate517 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![1, 1, -2, 0], ![1, 1, 2, -4]]⟩

def coordinate518 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate519 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate520 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 1, 1, -2], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate521 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 1, -2]]⟩

def coordinate522 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]⟩

def coordinate523 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate524 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate525 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate526 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate527 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -2, 1]]⟩

def coordinate528 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]⟩

def coordinate529 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 0, 0]]⟩

def coordinate530 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate531 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, -2, 0]]⟩

def coordinate532 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate533 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]⟩

def coordinate534 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]⟩

def coordinate535 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, -1, 1]]⟩

def coordinate536 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate537 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinate538 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 2, -2]]⟩

def coordinate539 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -2, 1, -1]]⟩

def coordinate540 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]⟩

def coordinate541 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]⟩

def coordinate542 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]⟩

def coordinate543 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![1, -2, 3, -2], ![1, 1, 0, -2]]⟩

def coordinate544 : ExponentCode := ⟨5, 4, ![![-2, 0, -1, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]⟩

def coordinate545 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -2, 0]]⟩

def coordinate546 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]⟩

def coordinate547 : ExponentCode := ⟨4, 4, ![![-2, 0, -1, 3], ![0, 2, 0, -2], ![1, -2, 3, -2], ![1, 0, -2, 1]]⟩

def coordinate548 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 2, 1], ![0, 1, 1, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate549 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 2, 1], ![0, 1, 1, -2], ![0, 2, -1, -1], ![2, 0, -2, 0]]⟩

def coordinate550 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 2, 1], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate551 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 2, 1], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]⟩

def coordinate552 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 2, 1], ![0, 2, -1, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]⟩

def coordinate553 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![0, 1, -2, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]⟩

def coordinate554 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![0, 1, -2, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]⟩

def coordinate555 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![0, 1, -2, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate556 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![0, 2, -1, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]⟩

def coordinate557 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -3, 3, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinate558 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, 0, -1, -1]]⟩

def coordinate559 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 0, 3, -3], ![1, 1, -2, 0], ![1, 1, -1, -1]]⟩

def coordinate560 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]⟩

def coordinate561 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, -1, 2, -1], ![0, 3, -2, -1], ![2, 0, -1, -1]]⟩

def coordinate562 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 2, -1, -2]]⟩

def coordinate563 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 2, -2, -1]]⟩

def coordinate564 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, -1, 2, -1], ![1, 1, 0, -2], ![1, 2, -3, 0]]⟩

def coordinate565 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, 0, 0, -2]]⟩

def coordinate566 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -3, 1]]⟩

def coordinate567 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![0, 3, -2, -1], ![2, -1, -1, 0]]⟩

def coordinate568 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 2, -2], ![1, 1, -3, 1], ![1, 1, 0, -2]]⟩

def coordinate569 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, -1, -1]]⟩

def coordinate570 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, -1, -1]]⟩

def coordinate571 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -3, 1]]⟩

def coordinate572 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 2, -3, 0]]⟩

def coordinate573 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -3, 1]]⟩

def coordinate574 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![0, 2, -2, 0], ![2, -1, -1, 0]]⟩

def coordinate575 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 2, -3], ![1, 0, -2, 1], ![1, 1, -1, -1]]⟩

def coordinateChunk8 : Array ExponentCode := #[coordinate512, coordinate513, coordinate514, coordinate515, coordinate516, coordinate517, coordinate518, coordinate519, coordinate520, coordinate521, coordinate522, coordinate523, coordinate524, coordinate525, coordinate526, coordinate527, coordinate528, coordinate529, coordinate530, coordinate531, coordinate532, coordinate533, coordinate534, coordinate535, coordinate536, coordinate537, coordinate538, coordinate539, coordinate540, coordinate541, coordinate542, coordinate543, coordinate544, coordinate545, coordinate546, coordinate547, coordinate548, coordinate549, coordinate550, coordinate551, coordinate552, coordinate553, coordinate554, coordinate555, coordinate556, coordinate557, coordinate558, coordinate559, coordinate560, coordinate561, coordinate562, coordinate563, coordinate564, coordinate565, coordinate566, coordinate567, coordinate568, coordinate569, coordinate570, coordinate571, coordinate572, coordinate573, coordinate574, coordinate575]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinate576 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -3, 1], ![1, 0, 1, -2], ![1, 0, 1, -2]]⟩

def coordinate577 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 1, -1, -1]]⟩

def coordinate578 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]⟩

def coordinate579 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, -2, 1], ![1, 0, 2, -3]]⟩

def coordinate580 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 0, -2, 2], ![1, 1, -1, -1], ![1, 1, 1, -3]]⟩

def coordinate581 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, 0, 0, -2]]⟩

def coordinate582 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -3, 2], ![1, 0, 1, -2], ![1, 1, 0, -2]]⟩

def coordinate583 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 2, -2, -1]]⟩

def coordinate584 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 1, -2], ![1, 0, -3, 2], ![1, 1, 0, -2]]⟩

def coordinate585 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate586 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]⟩

def coordinate587 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -3, 2], ![1, 0, 1, -2]]⟩

def coordinate588 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate589 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 3, -2, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]⟩

def coordinate590 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 3, -1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]⟩

def coordinate591 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![0, 0, -2, 2], ![1, 1, -1, -1], ![1, 1, 0, -2]]⟩

def coordinate592 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]⟩

def coordinate593 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]⟩

def coordinate594 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]⟩

def coordinate595 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]⟩

def coordinate596 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]⟩

def coordinate597 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]⟩

def coordinate598 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 1, -2]]⟩

def coordinate599 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]⟩

def coordinate600 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]⟩

def coordinate601 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate602 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 1, -2, 0]]⟩

def coordinate603 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -2, 0]]⟩

def coordinate604 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]⟩

def coordinate605 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 1, -2]]⟩

def coordinate606 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -1, 1, -2]]⟩

def coordinate607 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -1, 0, -1]]⟩

def coordinate608 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 0, -2]]⟩

def coordinate609 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]⟩

def coordinate610 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 2, -3, 0]]⟩

def coordinate611 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -2, 2], ![1, 1, -1, -1]]⟩

def coordinate612 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, -2, 2], ![1, 0, 1, -2]]⟩

def coordinate613 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -2, 1, 0], ![1, 1, -3, 1]]⟩

def coordinate614 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -3, 2]]⟩

def coordinate615 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 3, -1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]⟩

def coordinate616 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![2, -1, 0, -1]]⟩

def coordinate617 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, -1, -1, 0]]⟩

def coordinate618 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 0, -2]]⟩

def coordinate619 : ExponentCode := ⟨4, 4, ![![-2, 0, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![2, -1, -3, 2]]⟩

def coordinate620 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 1, -1]]⟩

def coordinate621 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]⟩

def coordinate622 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -1, -1]]⟩

def coordinate623 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -1, -1]]⟩

def coordinate624 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 2, -3]]⟩

def coordinate625 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]⟩

def coordinate626 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]⟩

def coordinate627 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 0, 0]]⟩

def coordinate628 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 0, -2]]⟩

def coordinate629 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, -1, 1]]⟩

def coordinate630 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -1, 2], ![1, 1, -2, 0]]⟩

def coordinate631 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1], ![1, 1, -3, 1]]⟩

def coordinate632 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -2, 0, 1], ![1, 0, 1, -2]]⟩

def coordinate633 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, -1, 2], ![1, 0, 1, -2]]⟩

def coordinate634 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]⟩

def coordinate635 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, -1, -1]]⟩

def coordinate636 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 0, 1], ![1, 0, -2, 1]]⟩

def coordinate637 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, -1, 1]]⟩

def coordinate638 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, 1, -2]]⟩

def coordinate639 : ExponentCode := ⟨5, 4, ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, -1, 1, -1]]⟩

def coordinateChunk9 : Array ExponentCode := #[coordinate576, coordinate577, coordinate578, coordinate579, coordinate580, coordinate581, coordinate582, coordinate583, coordinate584, coordinate585, coordinate586, coordinate587, coordinate588, coordinate589, coordinate590, coordinate591, coordinate592, coordinate593, coordinate594, coordinate595, coordinate596, coordinate597, coordinate598, coordinate599, coordinate600, coordinate601, coordinate602, coordinate603, coordinate604, coordinate605, coordinate606, coordinate607, coordinate608, coordinate609, coordinate610, coordinate611, coordinate612, coordinate613, coordinate614, coordinate615, coordinate616, coordinate617, coordinate618, coordinate619, coordinate620, coordinate621, coordinate622, coordinate623, coordinate624, coordinate625, coordinate626, coordinate627, coordinate628, coordinate629, coordinate630, coordinate631, coordinate632, coordinate633, coordinate634, coordinate635, coordinate636, coordinate637, coordinate638, coordinate639]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def coordinates (i : Fin 909) : ExponentCode :=
  ((#[coordinateChunk0, coordinateChunk1, coordinateChunk2, coordinateChunk3, coordinateChunk4, coordinateChunk5, coordinateChunk6, coordinateChunk7, coordinateChunk8, coordinateChunk9, coordinateChunk10, coordinateChunk11, coordinateChunk12, coordinateChunk13, coordinateChunk14])[i.val / 64]!)[i.val % 64]!

noncomputable def momentVector (H : CMatrix) : Fin 909 → ℝ :=
  fun i => (coordinates i).moment H

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

/-- The pair certificate coordinates averaged over ordered pairs of bases. -/
def familyPairVector (B : Fin 7 → Basis) : Fin 909 → ℝ :=
  fun i => familyAverage B (fun H => PairSemantics.momentVector H i)

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceB0 : Charge := ![0, 0, 0, 0, 2, -2]
def sourceC0 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC1 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA2 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB2 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceC2 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA3 : Charge := ![0, 0, 0, 1, 1, -2]
def sourceB3 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC3 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA4 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB4 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC4 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA5 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB5 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC5 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA6 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB6 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC6 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA7 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB7 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC7 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA8 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceB8 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC8 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA9 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB9 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC9 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA10 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceB10 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC10 : Charge := ![-2, 0, 0, 0, 0, 2]

def sourceA11 : Charge := ![-2, 0, 0, 0, 0, 2]
def sourceB11 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC11 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA12 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB12 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC12 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA13 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB13 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC13 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA14 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB14 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC14 : Charge := ![0, 0, 1, 1, -1, -1]

def sourceA15 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB15 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC15 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA16 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB16 : Charge := ![1, -1, 0, 0, -1, 1]
def sourceC16 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA17 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB17 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC17 : Charge := ![1, -1, 0, 0, -1, 1]

def sourceA18 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB18 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC18 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA19 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB19 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceC19 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA20 : Charge := ![1, -1, 0, 1, -1, 0]
def sourceB20 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC20 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA21 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB21 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC21 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA22 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB22 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC22 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA23 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB23 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC23 : Charge := ![-2, 0, 0, 0, 1, 1]

def sourceA24 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB24 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC24 : Charge := ![2, -1, 0, 0, -1, 0]

def sourceA25 : Charge := ![-2, 0, 0, 0, 1, 1]
def sourceB25 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC25 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA26 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB26 : Charge := ![0, 0, 1, 1, -1, -1]
def sourceC26 : Charge := ![1, 1, -1, -1, 0, 0]

def sourceA27 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB27 : Charge := ![0, 1, -1, 1, -1, 0]
def sourceC27 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA28 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB28 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC28 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA29 : Charge := ![-1, -1, 0, 0, 1, 1]
def sourceB29 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC29 : Charge := ![0, 0, 0, 0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA32 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB32 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC32 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA33 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB33 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC33 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA34 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB34 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC34 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA35 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB35 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC35 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA36 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB36 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC36 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA38 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB38 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC38 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA40 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB40 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC40 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA41 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB41 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC41 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA42 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB42 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC42 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA43 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB43 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC43 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA44 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB44 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC44 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA45 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB45 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC45 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA46 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB46 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC46 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA47 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB47 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC47 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA48 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB48 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC48 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA51 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB51 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC51 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA52 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB52 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC52 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA53 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB53 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC53 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA54 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB54 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC54 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA55 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB55 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC55 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA59 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB59 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC59 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA60 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB60 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC60 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA61 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB61 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC61 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA62 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB62 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC62 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA63 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB63 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC63 : Charge := ![3, 0, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA320 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB320 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC320 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA321 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB321 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC321 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA322 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB322 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC322 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA323 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB323 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC323 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA324 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB324 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC324 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA325 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB325 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC325 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA326 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB326 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC326 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA327 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB327 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC327 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA328 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB328 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC328 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA329 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB329 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC329 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA331 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB331 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC331 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA332 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB332 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC332 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA333 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB333 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC333 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA335 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB335 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC335 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA336 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB336 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC336 : Charge := ![2, 1, 0, -2, -1, 0]

def sourceA341 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB341 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC341 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA342 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB342 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC342 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA343 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB343 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC343 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA344 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB344 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC344 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA345 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB345 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC345 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA346 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB346 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC346 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA347 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB347 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC347 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA348 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB348 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC348 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA349 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB349 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC349 : Charge := ![1, -1, 0, 2, 0, -2]

def sourceA350 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB350 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC350 : Charge := ![1, -1, 0, 2, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA353 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB353 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC353 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA354 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB354 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC354 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA355 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB355 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC355 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA356 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB356 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC356 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA357 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB357 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC357 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA361 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB361 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC361 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA362 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB362 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC362 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA363 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB363 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC363 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA364 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB364 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC364 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA365 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB365 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC365 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA366 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB366 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC366 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA367 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB367 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC367 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA368 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB368 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC368 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA369 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB369 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC369 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA370 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB370 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC370 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA371 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB371 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC371 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA372 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB372 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC372 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA373 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB373 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC373 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA374 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB374 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC374 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA375 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB375 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC375 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA376 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB376 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC376 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA377 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB377 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC377 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA378 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB378 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC378 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA381 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB381 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC381 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA382 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB382 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC382 : Charge := ![2, 1, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA384 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB384 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC384 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA385 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB385 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC385 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA386 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB386 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC386 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA387 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB387 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC387 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA388 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB388 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC388 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA389 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB389 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC389 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA390 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB390 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC390 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA391 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB391 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC391 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA392 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB392 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC392 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA393 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB393 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC393 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA394 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB394 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC394 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA395 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB395 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC395 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA396 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB396 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC396 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA397 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB397 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC397 : Charge := ![1, -1, 1, 1, 0, -2]

def sourceA400 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB400 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC400 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA401 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB401 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC401 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA402 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB402 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC402 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA403 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB403 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC403 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA405 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB405 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC405 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA406 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB406 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC406 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA407 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB407 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC407 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA408 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB408 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC408 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA409 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB409 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC409 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA410 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB410 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC410 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA411 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB411 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC411 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA412 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB412 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC412 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA413 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB413 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC413 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA414 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB414 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC414 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA417 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB417 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC417 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA418 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB418 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC418 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA419 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB419 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC419 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA420 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB420 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC420 : Charge := ![2, 0, 0, 0, -3, 1]

def sourceA421 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB421 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC421 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA422 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB422 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC422 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA423 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB423 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC423 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA424 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB424 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC424 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA425 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB425 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC425 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA426 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB426 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC426 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA427 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB427 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC427 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA428 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB428 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC428 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA429 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB429 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC429 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA430 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB430 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC430 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA431 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB431 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC431 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA432 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB432 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC432 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA433 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB433 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC433 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA434 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB434 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC434 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA435 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB435 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC435 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA436 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB436 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC436 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA437 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB437 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC437 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA438 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB438 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC438 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA440 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB440 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC440 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA441 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB441 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC441 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA442 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB442 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC442 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA443 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB443 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC443 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA444 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB444 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC444 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA445 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB445 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC445 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA446 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB446 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC446 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA447 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB447 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC447 : Charge := ![2, 0, 0, -1, -2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA448 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB448 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC448 : Charge := ![2, 0, 0, -1, -2, 1]

def sourceA451 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB451 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC451 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA452 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB452 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC452 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA453 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB453 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC453 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA454 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB454 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC454 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA455 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB455 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC455 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA456 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB456 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC456 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA457 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB457 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC457 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA458 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB458 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC458 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA461 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB461 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC461 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA462 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB462 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC462 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA463 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB463 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC463 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA466 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB466 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC466 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA467 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB467 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC467 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA468 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB468 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC468 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA471 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB471 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC471 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA473 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB473 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC473 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA474 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB474 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC474 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA475 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB475 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC475 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA476 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB476 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC476 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA477 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB477 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC477 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA478 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB478 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC478 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA479 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB479 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC479 : Charge := ![1, 0, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA480 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB480 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC480 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA481 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB481 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC481 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA483 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB483 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC483 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA485 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB485 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC485 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA486 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB486 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC486 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA487 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB487 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC487 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA488 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB488 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC488 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA489 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB489 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC489 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA490 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB490 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC490 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA493 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB493 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC493 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA494 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB494 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC494 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA495 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB495 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC495 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA496 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC496 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA497 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC497 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA498 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB498 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC498 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA499 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB499 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC499 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA500 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB500 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC500 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA503 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB503 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC503 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA504 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB504 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC504 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA505 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB505 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC505 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA506 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB506 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC506 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA507 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB507 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC507 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA508 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB508 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC508 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA509 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB509 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC509 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA510 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB510 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC510 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA511 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB511 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC511 : Charge := ![1, 0, 1, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA512 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB512 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC512 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA513 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB513 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC513 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA514 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB514 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC514 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA515 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB515 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC515 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA516 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB516 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC516 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA517 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB517 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC517 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA518 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB518 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC518 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA519 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB519 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC519 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA520 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB520 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC520 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA521 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB521 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC521 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA523 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB523 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC523 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA525 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB525 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC525 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA526 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB526 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC526 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA527 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB527 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC527 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA528 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB528 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC528 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA529 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB529 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC529 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA530 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB530 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC530 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA531 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB531 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC531 : Charge := ![2, 0, -1, -1, 0, 0]

def sourceA532 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB532 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC532 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA533 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB533 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC533 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA534 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB534 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC534 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA535 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB535 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC535 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA536 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB536 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC536 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA537 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB537 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC537 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA538 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB538 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC538 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA539 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB539 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC539 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA540 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB540 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC540 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA541 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB541 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC541 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA544 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB544 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC544 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA545 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB545 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC545 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA546 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB546 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC546 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA547 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB547 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC547 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA548 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB548 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC548 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA549 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB549 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC549 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA550 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB550 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC550 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA551 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB551 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC551 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA552 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB552 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC552 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA553 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB553 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC553 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA554 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB554 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC554 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA555 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB555 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC555 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA556 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB556 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC556 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA557 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB557 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC557 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA560 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB560 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC560 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA561 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB561 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC561 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA562 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB562 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC562 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA564 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB564 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC564 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA565 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB565 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC565 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA566 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB566 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC566 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA567 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB567 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC567 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA568 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB568 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC568 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA569 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB569 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC569 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA570 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB570 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC570 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA571 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB571 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC571 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA572 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB572 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC572 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA573 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB573 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC573 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA574 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB574 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC574 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA575 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB575 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC575 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA576 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB576 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC576 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA577 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB577 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC577 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA578 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB578 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC578 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA579 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB579 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC579 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA580 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB580 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC580 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA581 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB581 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC581 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA582 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB582 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC582 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA583 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB583 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC583 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA584 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB584 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC584 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA585 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB585 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC585 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA586 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB586 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC586 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA587 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB587 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC587 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA588 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB588 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC588 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA589 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB589 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC589 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA590 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB590 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC590 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA591 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB591 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC591 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA592 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB592 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC592 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA593 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB593 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC593 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA594 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB594 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC594 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA595 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB595 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC595 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA596 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB596 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC596 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA597 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC597 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA598 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB598 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC598 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA599 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB599 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC599 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA600 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB600 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC600 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA601 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB601 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC601 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA602 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB602 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC602 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA603 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB603 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC603 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA604 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB604 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC604 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA605 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB605 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC605 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA606 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB606 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC606 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA607 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB607 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC607 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA608 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB608 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC608 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA609 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB609 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC609 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA610 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB610 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC610 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA611 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB611 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC611 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA612 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB612 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC612 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA613 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB613 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC613 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA614 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB614 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC614 : Charge := ![1, 0, 0, 0, -2, 1]

def sourceA615 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB615 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC615 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA616 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB616 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC616 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA617 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB617 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC617 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA618 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB618 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC618 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA619 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB619 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC619 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA620 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB620 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC620 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA621 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB621 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC621 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA622 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB622 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC622 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA623 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB623 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC623 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA624 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB624 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC624 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA625 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB625 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC625 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA626 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB626 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC626 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA627 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB627 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC627 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA628 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB628 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC628 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA629 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC629 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA630 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC630 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA631 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB631 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC631 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA632 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB632 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC632 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA633 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB633 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC633 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA634 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB634 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC634 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA635 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB635 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC635 : Charge := ![3, -2, 0, 0, -1, 0]

def sourceA636 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB636 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC636 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA637 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB637 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC637 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA638 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB638 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC638 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA639 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB639 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC639 : Charge := ![3, -2, 0, 0, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA64 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB64 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC64 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA65 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB65 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC65 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA68 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceB68 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC68 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA72 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB72 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC72 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA73 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB73 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC73 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA74 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB74 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC74 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA75 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB75 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC75 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA76 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB76 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC76 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA77 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB77 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC77 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA78 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB78 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC78 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA79 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB79 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC79 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA80 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB80 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC80 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA81 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB81 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC81 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA82 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB82 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC82 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA85 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB85 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC85 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA86 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB86 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC86 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA87 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB87 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC87 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA88 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB88 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC88 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA89 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB89 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC89 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA90 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB90 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC90 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA91 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB91 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC91 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA94 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB94 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC94 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA95 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB95 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC95 : Charge := ![2, 1, 0, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA640 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB640 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC640 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA641 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB641 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC641 : Charge := ![3, -2, 0, 0, 0, -1]

def sourceA642 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB642 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC642 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA643 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB643 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC643 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA644 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB644 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC644 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA645 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB645 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC645 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA646 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB646 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC646 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA647 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB647 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC647 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA648 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB648 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC648 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA649 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB649 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC649 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA650 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB650 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC650 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA651 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB651 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC651 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA652 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB652 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC652 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA653 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB653 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC653 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA654 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB654 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC654 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA655 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB655 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC655 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA656 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB656 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC656 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA657 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB657 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC657 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA658 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB658 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC658 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA659 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB659 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC659 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA660 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB660 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC660 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA661 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB661 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC661 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA662 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB662 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC662 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA663 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB663 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC663 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA664 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB664 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC664 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA665 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB665 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC665 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA666 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB666 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC666 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA667 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB667 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC667 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA668 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB668 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC668 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA669 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB669 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC669 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA670 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB670 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC670 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA671 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB671 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC671 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA672 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB672 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC672 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA673 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB673 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC673 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA674 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB674 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC674 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA675 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB675 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC675 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA676 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB676 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC676 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA677 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB677 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC677 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA678 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB678 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC678 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA679 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB679 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC679 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA680 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB680 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC680 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA681 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB681 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC681 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA683 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB683 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC683 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA684 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB684 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC684 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA685 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB685 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC685 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA686 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB686 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC686 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA687 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB687 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC687 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA688 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB688 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC688 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA689 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB689 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC689 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA690 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB690 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceC690 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA691 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB691 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC691 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA692 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB692 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC692 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA693 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB693 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC693 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA694 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB694 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC694 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA695 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB695 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC695 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA696 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB696 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC696 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA697 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB697 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC697 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA698 : Charge := ![1, -1, 1, -1, -1, 1]
def sourceB698 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC698 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA700 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB700 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC700 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA701 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB701 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC701 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA702 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB702 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC702 : Charge := ![2, 1, -2, 0, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA704 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB704 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC704 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA705 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB705 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceC705 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA706 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB706 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC706 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA707 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB707 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC707 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA708 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB708 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC708 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA709 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB709 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC709 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA710 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB710 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC710 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA711 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB711 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC711 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA713 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB713 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC713 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA714 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB714 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC714 : Charge := ![1, -1, 2, -1, -1, 0]

def sourceA715 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB715 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC715 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA716 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB716 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC716 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA717 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB717 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC717 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA718 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB718 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC718 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA719 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB719 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC719 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA720 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB720 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC720 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA721 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB721 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC721 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA722 : Charge := ![1, -1, 2, -1, -1, 0]
def sourceB722 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC722 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA723 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB723 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC723 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA724 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB724 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC724 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA725 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB725 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC725 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA726 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB726 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC726 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA727 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB727 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC727 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA728 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB728 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC728 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA729 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB729 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC729 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA731 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB731 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC731 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA732 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB732 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC732 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA733 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB733 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC733 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA734 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB734 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC734 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA735 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB735 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC735 : Charge := ![2, 0, -1, 1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA736 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB736 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC736 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA737 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB737 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC737 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA738 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB738 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC738 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA739 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB739 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC739 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA740 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB740 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC740 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA741 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB741 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC741 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA743 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB743 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC743 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA746 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB746 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC746 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA747 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB747 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC747 : Charge := ![1, 0, 1, -2, -1, 1]

def sourceA749 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB749 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC749 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA751 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB751 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC751 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA752 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB752 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC752 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA753 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB753 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC753 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA754 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB754 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC754 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA755 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB755 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC755 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA756 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB756 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC756 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA757 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB757 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC757 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA758 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB758 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC758 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA759 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB759 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC759 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA760 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB760 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC760 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA761 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB761 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC761 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA762 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB762 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC762 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA763 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB763 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC763 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA765 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB765 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC765 : Charge := ![2, 0, -2, 1, 0, -1]

def sourceA766 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB766 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC766 : Charge := ![2, 0, -2, 1, 0, -1]

def sourceA767 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB767 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC767 : Charge := ![2, 0, -2, 1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA768 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB768 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC768 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA769 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB769 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC769 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA770 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB770 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC770 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA771 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB771 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC771 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA772 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB772 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC772 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA773 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB773 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC773 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA774 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB774 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC774 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA775 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB775 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC775 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA776 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB776 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC776 : Charge := ![1, 0, 2, -2, -1, 0]

def sourceA778 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB778 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC778 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA780 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB780 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC780 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA781 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB781 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC781 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA782 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB782 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC782 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA783 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB783 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC783 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA784 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB784 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC784 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA785 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceB785 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC785 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA788 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB788 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC788 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA789 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB789 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC789 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA790 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB790 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC790 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA791 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB791 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC791 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA792 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB792 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC792 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA793 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB793 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC793 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA796 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB796 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC796 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA797 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB797 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC797 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA798 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB798 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC798 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA799 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB799 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC799 : Charge := ![2, -1, -1, 1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA800 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB800 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC800 : Charge := ![2, -1, -1, 1, 0, -1]

def sourceA801 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB801 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC801 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA802 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB802 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC802 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA803 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB803 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC803 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA804 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB804 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC804 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA805 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB805 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC805 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA806 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB806 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC806 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA807 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB807 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC807 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA809 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB809 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC809 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA811 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB811 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC811 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA812 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB812 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC812 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA813 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB813 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC813 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA814 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB814 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC814 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA815 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB815 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC815 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA816 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB816 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC816 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA817 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB817 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC817 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA818 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB818 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC818 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA819 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB819 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC819 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA820 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB820 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC820 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA821 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB821 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC821 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA822 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB822 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC822 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA823 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB823 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC823 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA824 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB824 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC824 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA825 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB825 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC825 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA826 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB826 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC826 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA827 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB827 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC827 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA828 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB828 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC828 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA829 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB829 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC829 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA830 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB830 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC830 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA831 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB831 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC831 : Charge := ![2, -1, 1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA832 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB832 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC832 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA833 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB833 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC833 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA834 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB834 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC834 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA835 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB835 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC835 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA836 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB836 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC836 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA837 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB837 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC837 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA838 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB838 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC838 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA839 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB839 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC839 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA840 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB840 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC840 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA841 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB841 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC841 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA842 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB842 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC842 : Charge := ![2, 0, 0, -2, -1, 1]

def sourceA843 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB843 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC843 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA844 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB844 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC844 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA845 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB845 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC845 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA846 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB846 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC846 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA847 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB847 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC847 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA848 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB848 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC848 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA849 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB849 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC849 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA850 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB850 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC850 : Charge := ![1, 0, -1, 1, 0, -1]

def sourceA851 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB851 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC851 : Charge := ![1, 0, -1, 1, 0, -1]

def sourceA852 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB852 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC852 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA853 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceB853 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC853 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA854 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB854 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC854 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA855 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB855 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC855 : Charge := ![-3, 0, 0, 1, 1, 1]

def sourceA856 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB856 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC856 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA857 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB857 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC857 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA858 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB858 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC858 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA859 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB859 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC859 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA860 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB860 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC860 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA862 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB862 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC862 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA863 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB863 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC863 : Charge := ![2, 1, -1, -2, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA864 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB864 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC864 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA865 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB865 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC865 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA866 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB866 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC866 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA867 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB867 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC867 : Charge := ![2, 1, -1, -2, 0, 0]

def sourceA868 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB868 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC868 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA869 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB869 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC869 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA870 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB870 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC870 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA871 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB871 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC871 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA872 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB872 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC872 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA873 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB873 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC873 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA874 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB874 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC874 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA875 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB875 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC875 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA876 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB876 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC876 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA877 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB877 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC877 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA878 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB878 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC878 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA879 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB879 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC879 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA882 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB882 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC882 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA883 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB883 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC883 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA884 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB884 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC884 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA885 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB885 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC885 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA886 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB886 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC886 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA887 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB887 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC887 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA888 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB888 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC888 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA889 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB889 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC889 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA890 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB890 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC890 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA891 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB891 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC891 : Charge := ![0, 1, -1, 1, 1, -2]

def sourceA893 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB893 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC893 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA894 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB894 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC894 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA895 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB895 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC895 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA896 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB896 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC896 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA897 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB897 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC897 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA898 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB898 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC898 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA899 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB899 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC899 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA901 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB901 : Charge := ![0, 1, -1, 2, 0, -2]
def sourceC901 : Charge := ![2, 0, 1, -2, -1, 0]

def sourceA903 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB903 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC903 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA904 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB904 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC904 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA905 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB905 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC905 : Charge := ![0, 1, 0, 0, 1, -2]

def sourceA906 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB906 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC906 : Charge := ![0, 1, 0, 0, 1, -2]

def sourceA907 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB907 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC907 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA908 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB908 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC908 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA909 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB909 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC909 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA910 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB910 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC910 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA911 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB911 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC911 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA912 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB912 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC912 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA913 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB913 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC913 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA914 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB914 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC914 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA915 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB915 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC915 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA916 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB916 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC916 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA917 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceB917 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC917 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA919 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB919 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC919 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA920 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB920 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC920 : Charge := ![2, 0, 0, -2, 1, -1]

def sourceA923 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB923 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC923 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA924 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB924 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC924 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA925 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB925 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC925 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA926 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB926 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC926 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA927 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB927 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC927 : Charge := ![0, 1, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA928 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB928 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC928 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA929 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB929 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC929 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA930 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB930 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC930 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA931 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB931 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC931 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA932 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB932 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC932 : Charge := ![2, 0, 0, -2, 0, 0]

def sourceA933 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB933 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC933 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA934 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB934 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC934 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA935 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB935 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC935 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA936 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB936 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC936 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA937 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB937 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC937 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA938 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB938 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC938 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA940 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB940 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC940 : Charge := ![2, 0, -1, -1, 1, -1]

def sourceA941 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB941 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC941 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA942 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB942 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC942 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA943 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB943 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC943 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA944 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB944 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC944 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA945 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB945 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC945 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA946 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB946 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC946 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA947 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB947 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC947 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA948 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB948 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC948 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA949 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB949 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC949 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA950 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB950 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC950 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA951 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB951 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC951 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA952 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB952 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC952 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA954 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB954 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC954 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA955 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB955 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC955 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA956 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB956 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC956 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA957 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB957 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC957 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA958 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB958 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC958 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA959 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB959 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC959 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA96 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB96 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC96 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA97 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB97 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC97 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA98 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB98 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC98 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA99 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB99 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC99 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA100 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB100 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC100 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA101 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB101 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC101 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA102 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB102 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC102 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA103 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB103 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC103 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA106 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB106 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC106 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA107 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB107 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC107 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA108 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB108 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC108 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA109 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB109 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC109 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA110 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB110 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC110 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA111 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB111 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC111 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA112 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB112 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC112 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA113 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB113 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC113 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA114 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB114 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC114 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA115 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB115 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC115 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA116 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB116 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC116 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA117 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB117 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC117 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA118 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB118 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC118 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA119 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB119 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC119 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA120 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB120 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC120 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA121 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB121 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC121 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA122 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB122 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC122 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA123 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB123 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC123 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA124 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB124 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC124 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA125 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB125 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC125 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA126 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB126 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC126 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA127 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB127 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC127 : Charge := ![1, 0, 0, 0, 2, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA960 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB960 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC960 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA963 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB963 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC963 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA964 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB964 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC964 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA965 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB965 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC965 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA966 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB966 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC966 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA967 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB967 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC967 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA968 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB968 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC968 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA969 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB969 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC969 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA972 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB972 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC972 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA973 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB973 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC973 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA976 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB976 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC976 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA977 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB977 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC977 : Charge := ![2, -1, 1, -1, 0, -1]

def sourceA978 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB978 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC978 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA979 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB979 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC979 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA980 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB980 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC980 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA982 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB982 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC982 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA983 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB983 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC983 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA986 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB986 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC986 : Charge := ![0, 2, -1, 1, -1, -1]

def sourceA987 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB987 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC987 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA988 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB988 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC988 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA989 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB989 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC989 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA990 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB990 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC990 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA991 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB991 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC991 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA992 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceB992 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC992 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA993 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB993 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC993 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA994 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB994 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC994 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA995 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB995 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC995 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA996 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC996 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA997 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC997 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1000 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1000 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1000 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1001 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1001 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1001 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1003 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1003 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC1003 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1004 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1004 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1004 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1005 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1005 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1005 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1006 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1006 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1006 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1008 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1008 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1008 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1012 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1012 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1012 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1013 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1013 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1013 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA1015 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1015 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1015 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1016 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1016 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1016 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1017 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1017 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1017 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1018 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB1018 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1018 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1020 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1020 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1020 : Charge := ![2, -1, 0, -1, 0, 0]

def sourceA1021 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1021 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1021 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1022 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1022 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1022 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1023 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1023 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1023 : Charge := ![-2, -1, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1024 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1024 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC1024 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1025 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1025 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1025 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA1026 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1026 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1026 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA1027 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1027 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1027 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA1029 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1029 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1029 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA1030 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1030 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1030 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1031 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1031 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1031 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1032 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1032 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1032 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1033 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceB1033 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC1033 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1036 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1036 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1036 : Charge := ![1, 1, 1, -2, 0, -1]

def sourceA1039 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1039 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1039 : Charge := ![1, 1, 1, -2, 0, -1]

def sourceA1040 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceB1040 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1040 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1041 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceB1041 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC1041 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1043 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1043 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1043 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA1044 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1044 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1044 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA1045 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB1045 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1045 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1048 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1048 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1048 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1049 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1049 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1049 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1050 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1050 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1050 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1051 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1051 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC1051 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1052 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1052 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1052 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1053 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1053 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1053 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1054 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1054 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC1054 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1055 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1055 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1055 : Charge := ![1, 0, 1, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1056 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1056 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1056 : Charge := ![1, 0, 1, 0, -2, 0]

def sourceA1057 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB1057 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1057 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1058 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB1058 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1058 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1059 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1059 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1059 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA1060 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1060 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1060 : Charge := ![1, 0, 1, -1, 0, -1]

def sourceA1061 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1061 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1061 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1062 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB1062 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1062 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1063 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1063 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1063 : Charge := ![1, 1, -1, 1, 0, -2]

def sourceA1064 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1064 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1064 : Charge := ![1, 1, -1, 1, 0, -2]

def sourceA1065 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1065 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1065 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA1066 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1066 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1066 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA1067 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1067 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1067 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1068 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB1068 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1068 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1069 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1069 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1069 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1070 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1070 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1070 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1071 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1071 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1071 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1072 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1072 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1072 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1073 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1073 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1073 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA1074 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1074 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1074 : Charge := ![1, 0, 0, -1, 1, -1]

def sourceA1075 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1075 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1075 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1076 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1076 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1076 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1077 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1077 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1077 : Charge := ![1, 1, 0, 1, -1, -2]

def sourceA1078 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB1078 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceC1078 : Charge := ![-2, -1, 0, 0, 1, 2]

def sourceA1079 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1079 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1079 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA1080 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1080 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC1080 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA1081 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1081 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1081 : Charge := ![1, -1, 1, 0, -1, 0]

def sourceA1082 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1082 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1082 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA1083 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1083 : Charge := ![1, -1, 0, 0, 1, -1]
def sourceC1083 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA1084 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1084 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1084 : Charge := ![1, -1, 0, 0, 1, -1]

def sourceA1085 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1085 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1085 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1086 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1086 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC1086 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1087 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1087 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1087 : Charge := ![0, 2, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1088 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1088 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1088 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA1089 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1089 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC1089 : Charge := ![2, -1, 0, 1, 0, -2]

def sourceA1090 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1090 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC1090 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA1091 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1091 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1091 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA1092 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1092 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1092 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA1093 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1093 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC1093 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA1094 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1094 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1094 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1095 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1095 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC1095 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1096 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB1096 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1096 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1097 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1097 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC1097 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1098 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1098 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC1098 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA1099 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1099 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1099 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA1100 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB1100 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1100 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1101 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1101 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC1101 : Charge := ![2, 0, -2, 0, 0, 0]

def sourceA1102 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1102 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1102 : Charge := ![0, 1, 2, -1, -1, -1]

def sourceA1103 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1103 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1103 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA1104 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB1104 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1104 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1105 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1105 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1105 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA1106 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1106 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC1106 : Charge := ![2, -1, -1, 0, 0, 0]

def sourceA1107 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1107 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1107 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA1108 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB1108 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1108 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1109 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB1109 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1109 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1110 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1110 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1110 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1111 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1111 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1111 : Charge := ![1, 0, 0, -1, -1, 1]

def sourceA1112 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1112 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1112 : Charge := ![1, 1, -1, 1, 0, -2]

def sourceA1113 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1113 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1113 : Charge := ![1, 1, -1, 1, 0, -2]

def sourceA1114 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1114 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC1114 : Charge := ![1, 1, -1, 1, 0, -2]

def sourceA1116 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1116 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC1116 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA1117 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1117 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1117 : Charge := ![1, 0, 1, -1, -1, 0]

def sourceA1118 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1118 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1118 : Charge := ![1, 0, 1, 0, 0, -2]

def sourceA1119 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1119 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1119 : Charge := ![1, 0, 1, 0, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1120 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB1120 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1120 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1121 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB1121 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1121 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1122 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1122 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1122 : Charge := ![1, 1, 0, -2, -1, 1]

def sourceA1123 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1123 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1123 : Charge := ![1, 1, 0, -2, -1, 1]

def sourceA1124 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1124 : Charge := ![1, 1, 0, -2, -1, 1]
def sourceC1124 : Charge := ![1, 0, 0, 1, 0, -2]

def sourceA1125 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1125 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1125 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1126 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1126 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC1126 : Charge := ![1, 0, -1, 1, 0, -1]

def sourceA1127 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB1127 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1127 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1128 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1128 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1128 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA1129 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1129 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC1129 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA1130 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1130 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1130 : Charge := ![1, -1, 1, 0, 0, -1]

def sourceA1131 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1131 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1131 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA1132 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1132 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1132 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1133 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1133 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC1133 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1134 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1134 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1134 : Charge := ![0, 2, -1, 0, 0, -1]

def sourceA1135 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1135 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1135 : Charge := ![0, 2, -1, 0, 0, -1]

def sourceA1136 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceB1136 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1136 : Charge := ![-2, -1, 0, 1, 1, 1]

def sourceA1137 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1137 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1137 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1138 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1138 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC1138 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1139 : Charge := ![-2, -1, 0, 1, 1, 1]
def sourceB1139 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1139 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1140 : Charge := ![-1, -1, -1, 1, 1, 1]
def sourceB1140 : Charge := ![-1, 1, 1, -1, -1, 1]
def sourceC1140 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1141 : Charge := ![-1, -1, -1, 1, 1, 1]
def sourceB1141 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1141 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1142 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1142 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1142 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1143 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1143 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1143 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1145 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1145 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1145 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1147 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1147 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1147 : Charge := ![3, 0, 0, -1, -1, -1]

def sourceA1148 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1148 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC1148 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1150 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1150 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1150 : Charge := ![1, 0, 0, 1, 2, -4]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1152 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1152 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1152 : Charge := ![2, 1, 0, 0, -1, -2]

def sourceA1153 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1153 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1153 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1154 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1154 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1154 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1155 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1155 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1155 : Charge := ![2, -1, 0, 0, 2, -3]

def sourceA1156 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1156 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1156 : Charge := ![2, -1, 0, 0, 2, -3]

def sourceA1157 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1157 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1157 : Charge := ![2, -1, 0, 1, 1, -3]

def sourceA1158 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1158 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1158 : Charge := ![2, -1, 0, 1, 1, -3]

def sourceA1159 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1159 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1159 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1160 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1160 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1160 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1161 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1161 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1161 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1162 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1162 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1162 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1163 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1164 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1164 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1164 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1165 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1165 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1165 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1166 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1166 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1166 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1167 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1167 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1167 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1168 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1168 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1168 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1169 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1169 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1169 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1170 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1170 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1170 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1171 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1171 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1171 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1172 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1172 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1172 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1173 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1173 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1173 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1177 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1177 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1177 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1178 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1178 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1178 : Charge := ![2, 0, 0, 0, 2, -4]

def sourceA1179 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1179 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1179 : Charge := ![2, 0, 0, 0, 2, -4]

def sourceA1180 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1180 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1180 : Charge := ![2, 0, 0, 0, 2, -4]

def sourceA1182 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1182 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1182 : Charge := ![2, 0, 0, 1, 1, -4]

def sourceA1183 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1183 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1183 : Charge := ![2, 0, 0, 1, 1, -4]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1184 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1184 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1184 : Charge := ![2, 0, 0, 1, 1, -4]

def sourceA1186 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1186 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1186 : Charge := ![3, -1, 0, 0, 1, -3]

def sourceA1189 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1189 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1189 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1190 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1190 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1190 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1191 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1191 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1191 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1192 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB1192 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1192 : Charge := ![-4, 0, 0, 0, 0, 4]

def sourceA1193 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1193 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1193 : Charge := ![3, 0, 0, 0, 1, -4]

def sourceA1194 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1194 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1194 : Charge := ![3, 0, 0, 0, 1, -4]

def sourceA1195 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1195 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1195 : Charge := ![3, 0, 0, 0, 1, -4]

def sourceA1197 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1197 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1197 : Charge := ![3, 0, 0, 0, 1, -4]

def sourceA1198 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1198 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1198 : Charge := ![3, 0, 0, 0, 1, -4]

def sourceA1200 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1200 : Charge := ![4, 0, 0, 0, 0, -4]
def sourceC1200 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1201 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1201 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC1201 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1202 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1202 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1202 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1203 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1203 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1203 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1204 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB1204 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1204 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1205 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1205 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1205 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA1206 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1206 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC1206 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA1207 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1207 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1207 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA1208 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1208 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1208 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1210 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1210 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1210 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1211 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB1211 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1211 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1212 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1212 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1212 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA1213 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1213 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1213 : Charge := ![1, 0, 0, 2, -1, -2]

def sourceA1214 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1214 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1214 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1215 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1215 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1215 : Charge := ![-4, 0, 0, 0, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1216 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1216 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1216 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1217 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1217 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1217 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1218 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1218 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1218 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1220 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1220 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1220 : Charge := ![1, 0, 0, 2, 0, -3]

def sourceA1221 : Charge := ![1, 0, 0, 2, 0, -3]
def sourceB1221 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1221 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1224 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1224 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1224 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA1225 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1225 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1225 : Charge := ![1, 0, 1, 1, -1, -2]

def sourceA1226 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1226 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1226 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1228 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1228 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1228 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1229 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1229 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1229 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1231 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1231 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC1231 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA1232 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1232 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1232 : Charge := ![1, 0, 1, 1, 0, -3]

def sourceA1233 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceB1233 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC1233 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1235 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1235 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1235 : Charge := ![1, 0, 1, 2, -1, -3]

def sourceA1237 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1237 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1237 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA1238 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1238 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1238 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA1239 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1239 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1239 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1240 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1240 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1240 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1241 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1241 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1241 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1242 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1242 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1242 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1243 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1243 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1243 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1244 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1244 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1244 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1246 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1246 : Charge := ![2, -1, 0, 0, 2, -3]

def sourceA1247 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1247 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1247 : Charge := ![2, 1, 0, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1248 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1248 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1248 : Charge := ![2, 1, 0, -1, 0, -2]

def sourceA1249 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1249 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1249 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1250 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1250 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1250 : Charge := ![2, -1, 0, 1, -1, -1]

def sourceA1251 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1251 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1251 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1252 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1252 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1252 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1253 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1253 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1253 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1254 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1254 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1254 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1255 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1255 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1255 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1256 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1256 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1256 : Charge := ![2, -1, 0, 1, 1, -3]

def sourceA1257 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1257 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1257 : Charge := ![2, -1, 0, 2, -1, -2]

def sourceA1258 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1258 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1258 : Charge := ![2, -1, 0, 2, -1, -2]

def sourceA1259 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1259 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC1259 : Charge := ![2, -1, 0, 2, 0, -3]

def sourceA1260 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1260 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1260 : Charge := ![2, -1, 1, 1, -1, -2]

def sourceA1261 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1261 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1261 : Charge := ![2, -1, 1, 1, -1, -2]

def sourceA1262 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1262 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1262 : Charge := ![2, -1, 1, 1, 0, -3]

def sourceA1263 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1263 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1263 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1264 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1264 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1264 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1265 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1265 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1265 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1266 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1266 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1266 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1267 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1267 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1267 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1268 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1268 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1268 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1269 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1269 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1269 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1270 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1270 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1270 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1271 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1271 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1271 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1272 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1272 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1272 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1273 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1273 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1273 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1274 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1274 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1274 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1275 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1275 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1275 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1276 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1276 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1276 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1277 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1277 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1277 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA1278 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1278 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1278 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1279 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1279 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1279 : Charge := ![2, 0, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA128 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB128 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC128 : Charge := ![1, 0, 0, 0, 2, -3]

def sourceA129 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB129 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC129 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA130 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB130 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC130 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA131 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB131 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC131 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA132 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceB132 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC132 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA133 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB133 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC133 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA134 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB134 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceC134 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA135 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB135 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC135 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA136 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB136 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC136 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA137 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB137 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC137 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA138 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB138 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC138 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA139 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB139 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC139 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA140 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB140 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC140 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA141 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB141 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC141 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA142 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB142 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC142 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA143 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB143 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC143 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA144 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB144 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC144 : Charge := ![1, 0, 0, 1, 1, -3]

def sourceA145 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB145 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC145 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA146 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB146 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC146 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA147 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB147 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC147 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA148 : Charge := ![1, 0, 0, 1, 1, -3]
def sourceB148 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC148 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA149 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB149 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC149 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA150 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB150 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC150 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA151 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB151 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC151 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA152 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB152 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC152 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA153 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB153 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC153 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA154 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB154 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC154 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA155 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB155 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC155 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA156 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB156 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC156 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA157 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB157 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC157 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA158 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB158 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC158 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA159 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB159 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC159 : Charge := ![-3, 0, 0, 0, 0, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1281 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1281 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1281 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1282 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1282 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1282 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1283 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1283 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1283 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1284 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1284 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1284 : Charge := ![2, 0, 0, 0, 2, -4]

def sourceA1285 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1285 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1285 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1286 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1286 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1286 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1287 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1287 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1287 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1288 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1288 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1288 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1289 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1289 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1289 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1290 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1290 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1290 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA1291 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1291 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1291 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1292 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1292 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1292 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1295 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1295 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC1295 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1296 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1296 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1296 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1297 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1297 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1297 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1298 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1298 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1298 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1299 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1299 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1299 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1300 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1300 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1300 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1301 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1301 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1301 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1302 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1302 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1302 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA1303 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1303 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1303 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1304 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1304 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1304 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1307 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1307 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1307 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1308 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1308 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceC1308 : Charge := ![2, 0, 0, 1, 1, -4]

def sourceA1309 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1309 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1309 : Charge := ![2, 0, 0, 2, -2, -2]

def sourceA1310 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1310 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1310 : Charge := ![2, 0, 0, 2, -2, -2]

def sourceA1311 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1311 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1311 : Charge := ![2, 0, 0, 2, -1, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1312 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1312 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1312 : Charge := ![2, 0, 0, 2, -1, -3]

def sourceA1313 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1313 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1313 : Charge := ![2, 0, 0, 2, -1, -3]

def sourceA1315 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1315 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceC1315 : Charge := ![2, 0, 0, 2, 0, -4]

def sourceA1316 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1316 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1316 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA1317 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1317 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1317 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA1318 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1318 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1318 : Charge := ![2, 0, 1, 1, -1, -3]

def sourceA1319 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1319 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1319 : Charge := ![2, 0, 1, 1, -1, -3]

def sourceA1320 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1320 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1320 : Charge := ![2, 0, 1, 1, -1, -3]

def sourceA1322 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1322 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1322 : Charge := ![2, 0, 1, 1, 0, -4]

def sourceA1323 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1323 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1323 : Charge := ![3, -2, 0, 0, 1, -2]

def sourceA1324 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1324 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1324 : Charge := ![3, -2, 0, 0, 1, -2]

def sourceA1325 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1325 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1325 : Charge := ![3, -2, 0, 1, -1, -1]

def sourceA1326 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1326 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1326 : Charge := ![3, -2, 0, 1, -1, -1]

def sourceA1327 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1327 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1327 : Charge := ![3, -2, 0, 1, 0, -2]

def sourceA1328 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1328 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1328 : Charge := ![3, -2, 0, 1, 0, -2]

def sourceA1329 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1329 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1329 : Charge := ![3, -1, -1, 0, 1, -2]

def sourceA1330 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1330 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1330 : Charge := ![3, -1, -1, 0, 1, -2]

def sourceA1331 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1331 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1331 : Charge := ![3, -1, -1, 1, -1, -1]

def sourceA1332 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1332 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1332 : Charge := ![3, -1, -1, 1, -1, -1]

def sourceA1333 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1333 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1333 : Charge := ![3, -1, -1, 1, 0, -2]

def sourceA1334 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1334 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1334 : Charge := ![3, -1, -1, 1, 0, -2]

def sourceA1335 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1335 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1335 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1336 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1336 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1336 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1337 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1337 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1337 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1338 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1338 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1338 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1339 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1339 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1339 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1340 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1340 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1340 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1341 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1341 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1341 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1342 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1342 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1342 : Charge := ![1, 1, 0, 0, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1344 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1344 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1344 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1345 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1345 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1345 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1347 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1347 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1347 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1348 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1348 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1348 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1349 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1349 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1349 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1350 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1350 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1350 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1351 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1351 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1351 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1352 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1352 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1352 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1353 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1353 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1353 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1354 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1354 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1354 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1355 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1355 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1355 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1356 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1356 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1356 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1357 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1357 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1357 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1360 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1360 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1360 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1361 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1361 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1361 : Charge := ![3, -1, 0, 0, 1, -3]

def sourceA1362 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1362 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1362 : Charge := ![3, -1, 0, 0, 1, -3]

def sourceA1363 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1363 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1363 : Charge := ![3, -1, 0, 0, 1, -3]

def sourceA1364 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB1364 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceC1364 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1366 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1366 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1366 : Charge := ![3, -1, 0, 1, -2, -1]

def sourceA1367 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1367 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1367 : Charge := ![3, -1, 0, 1, -1, -2]

def sourceA1370 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1370 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1370 : Charge := ![3, -1, 0, 1, -1, -2]

def sourceA1373 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1373 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1373 : Charge := ![3, -1, 0, 1, 0, -3]

def sourceA1375 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1375 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1375 : Charge := ![3, -1, 0, 1, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1376 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1376 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1376 : Charge := ![3, -1, 0, 1, 0, -3]

def sourceA1377 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1377 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceC1377 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1378 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1378 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1378 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1379 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1379 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1379 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1380 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1380 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1380 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1381 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1381 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1381 : Charge := ![1, 0, 0, 0, 1, -2]

def sourceA1385 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1385 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1385 : Charge := ![3, 0, 0, 0, -1, -2]

def sourceA1386 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1386 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1386 : Charge := ![3, 0, 0, 0, -1, -2]

def sourceA1387 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1387 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1387 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1388 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1388 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1388 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1389 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1389 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1389 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1390 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1390 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1390 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1391 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1391 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1391 : Charge := ![3, 0, 0, 1, -3, -1]

def sourceA1392 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1392 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1392 : Charge := ![3, 0, 0, 1, -3, -1]

def sourceA1393 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1393 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1393 : Charge := ![3, 0, 0, 1, -2, -2]

def sourceA1396 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1396 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1396 : Charge := ![3, 0, 0, 1, -2, -2]

def sourceA1399 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1399 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1399 : Charge := ![3, 0, 0, 1, -1, -3]

def sourceA1400 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1400 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1400 : Charge := ![3, 0, 0, 1, -1, -3]

def sourceA1401 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1401 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1401 : Charge := ![3, 0, 0, 1, -1, -3]

def sourceA1403 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1403 : Charge := ![0, 2, 1, 0, 0, -3]
def sourceC1403 : Charge := ![4, -2, -1, 0, -1, 0]

def sourceA1405 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1405 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1405 : Charge := ![4, -2, 0, 0, -2, 0]

def sourceA1406 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1406 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1406 : Charge := ![4, -2, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1408 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1408 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1408 : Charge := ![4, -2, 0, 0, -1, -1]

def sourceA1410 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1410 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1410 : Charge := ![4, -2, 0, 0, 0, -2]

def sourceA1411 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1411 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1411 : Charge := ![4, -2, 0, 0, 0, -2]

def sourceA1412 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1412 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1412 : Charge := ![4, -2, 0, 0, 0, -2]

def sourceA1413 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB1413 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceC1413 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1415 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1415 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1415 : Charge := ![4, -1, -1, -1, 0, -1]

def sourceA1417 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1417 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1417 : Charge := ![4, -1, -1, 0, -1, -1]

def sourceA1418 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1418 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1418 : Charge := ![4, -1, -1, 0, -1, -1]

def sourceA1419 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1419 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1419 : Charge := ![4, -1, -1, 0, -1, -1]

def sourceA1421 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1421 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1421 : Charge := ![4, -1, -1, 0, 0, -2]

def sourceA1422 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1422 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1422 : Charge := ![4, -1, -1, 0, 0, -2]

def sourceA1423 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1423 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1423 : Charge := ![4, -1, -1, 0, 0, -2]

def sourceA1424 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB1424 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceC1424 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1425 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1425 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1425 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1426 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1426 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1426 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1427 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1427 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1427 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1429 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1429 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1429 : Charge := ![4, -1, 0, 0, -1, -2]

def sourceA1430 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1430 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1430 : Charge := ![4, -1, 0, 0, -1, -2]

def sourceA1431 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1431 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1431 : Charge := ![4, -1, 0, 0, -1, -2]

def sourceA1433 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1433 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1433 : Charge := ![4, -1, 0, 0, -1, -2]

def sourceA1435 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1435 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1435 : Charge := ![4, -1, 0, 0, 0, -3]

def sourceA1437 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1437 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC1437 : Charge := ![4, 0, 0, 0, -2, -2]

def sourceA1438 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceB1438 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1438 : Charge := ![-4, 0, 0, 0, 1, 3]

def sourceA1439 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1439 : Charge := ![4, 0, 0, 0, -1, -3]
def sourceC1439 : Charge := ![0, 0, 0, 0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1440 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1440 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1440 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA1441 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1441 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1441 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA1443 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1443 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1443 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1444 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1444 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1444 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1445 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1445 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1445 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1448 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1448 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC1448 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA1449 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1449 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1449 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA1450 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1450 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1450 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1452 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1452 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1452 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1453 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1453 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1453 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1455 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1455 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1455 : Charge := ![1, 0, 1, 2, -2, -2]

def sourceA1457 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1457 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceC1457 : Charge := ![2, 1, 0, 0, 0, -3]

def sourceA1458 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1458 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1458 : Charge := ![2, -1, 0, 0, -2, 1]

def sourceA1459 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1459 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1459 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1460 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1460 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1460 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1461 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1461 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1461 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1462 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1462 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1462 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1463 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1463 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1463 : Charge := ![2, 1, 0, -1, 0, -2]

def sourceA1464 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1464 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1464 : Charge := ![2, 1, 0, -1, 0, -2]

def sourceA1465 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceB1465 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1465 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1467 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1467 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1467 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA1468 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1468 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1468 : Charge := ![2, 1, 0, -1, -1, -1]

def sourceA1469 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1469 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1469 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1470 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1470 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1470 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1471 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1471 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1471 : Charge := ![2, -1, 0, 2, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1472 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1472 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1472 : Charge := ![2, -1, 1, 1, -2, -1]

def sourceA1473 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1473 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1473 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1474 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1474 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1474 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1475 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1475 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1475 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1476 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1476 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1476 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1477 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1477 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1477 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1478 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1478 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1478 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1479 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1479 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1479 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1480 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1480 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1480 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1481 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1481 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1481 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1482 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1482 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1482 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1483 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1483 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1483 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1484 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1484 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1484 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1485 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1485 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1485 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1486 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1486 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1486 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1487 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1487 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1487 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1488 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1488 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1488 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1489 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1489 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1489 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA1490 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1490 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1490 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1491 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1491 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1491 : Charge := ![2, 0, 0, -1, 0, -1]

def sourceA1495 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1495 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1495 : Charge := ![2, 0, 0, 2, -3, -1]

def sourceA1496 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1496 : Charge := ![2, 0, 0, 2, -2, -2]

def sourceA1497 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC1497 : Charge := ![2, 0, 0, 2, -2, -2]

def sourceA1499 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1499 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC1499 : Charge := ![2, 0, 1, 1, -3, -1]

def sourceA1500 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1500 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1500 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA1501 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1501 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1501 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA1503 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1503 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1503 : Charge := ![3, -2, 0, 0, -2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1504 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1504 : Charge := ![1, 2, 0, -1, 0, -2]
def sourceC1504 : Charge := ![3, -2, 0, 1, -2, 0]

def sourceA1505 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1505 : Charge := ![1, 2, 0, -1, -1, -1]
def sourceC1505 : Charge := ![3, -2, 0, 1, -1, -1]

def sourceA1506 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1506 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1506 : Charge := ![3, -1, -1, 0, -2, 1]

def sourceA1507 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1507 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1507 : Charge := ![3, -1, -1, 1, -2, 0]

def sourceA1508 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1508 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1508 : Charge := ![3, -1, -1, 1, -1, -1]

def sourceA1509 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1509 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1509 : Charge := ![3, -1, 0, 0, -3, 1]

def sourceA1510 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1510 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1510 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1511 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1511 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1511 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1512 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1512 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1512 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1513 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1513 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1513 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1514 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1514 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1514 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1515 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1515 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1515 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1516 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1516 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1516 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1517 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1517 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1517 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1518 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1518 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC1518 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1522 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1522 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1522 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1523 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1523 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1523 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1524 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1524 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1524 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1525 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1525 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1525 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1526 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1526 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1526 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1527 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1527 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1527 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1528 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1528 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1528 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA1529 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1529 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1529 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1531 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1531 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1531 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1532 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1532 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1532 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1533 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1533 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC1533 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1534 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1534 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC1534 : Charge := ![3, -1, 0, 1, -3, 0]

def sourceA1535 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1535 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1535 : Charge := ![3, -1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1537 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1537 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1537 : Charge := ![3, -1, 0, 1, -2, -1]

def sourceA1538 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1538 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceC1538 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1540 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1540 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1540 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1541 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1541 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1541 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1542 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1542 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1542 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1543 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1543 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1543 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1550 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1550 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1550 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1551 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1551 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1551 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1552 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1552 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1552 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA1553 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB1553 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1553 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1554 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1554 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1554 : Charge := ![3, 0, 0, 1, -3, -1]

def sourceA1556 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1556 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1556 : Charge := ![3, 0, 0, 1, -2, -2]

def sourceA1558 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1558 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1558 : Charge := ![3, 0, 0, 1, -2, -2]

def sourceA1561 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1561 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1561 : Charge := ![4, -2, 0, 0, -2, 0]

def sourceA1562 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1562 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1562 : Charge := ![4, -2, 0, 0, -1, -1]

def sourceA1564 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1564 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1564 : Charge := ![4, -1, -1, 0, -2, 0]

def sourceA1565 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1565 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1565 : Charge := ![4, -1, -1, 0, -2, 0]

def sourceA1566 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB1566 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceC1566 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1567 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1567 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1567 : Charge := ![4, -1, -1, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1568 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1568 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1568 : Charge := ![4, -1, -1, 0, -1, -1]

def sourceA1569 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1569 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1569 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1570 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1570 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1570 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1571 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1571 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1571 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1572 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1572 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1572 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1573 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1573 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1573 : Charge := ![4, -1, 0, 0, -2, -1]

def sourceA1574 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB1574 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceC1574 : Charge := ![-4, 0, 0, 0, 2, 2]

def sourceA1575 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1575 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1575 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1576 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceB1576 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1576 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1577 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceB1577 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1577 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1578 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1578 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC1578 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA1579 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1579 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1579 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA1580 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1580 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1580 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1581 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1581 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1581 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1582 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1582 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1582 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1583 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceB1583 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC1583 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1584 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1584 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC1584 : Charge := ![3, 0, -2, 0, 0, -1]

def sourceA1585 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1585 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1585 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA1586 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1586 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1586 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1587 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1587 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1587 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1588 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceB1588 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC1588 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1590 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1590 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1590 : Charge := ![1, 0, 2, -1, 0, -2]

def sourceA1591 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB1591 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1591 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1592 : Charge := ![1, 0, 2, -1, 0, -2]
def sourceB1592 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC1592 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1594 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1594 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC1594 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA1595 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1595 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1595 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1596 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1596 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1596 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1597 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1597 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1597 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1598 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB1598 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC1598 : Charge := ![-4, 0, 0, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA160 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB160 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC160 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA161 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB161 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC161 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA162 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB162 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC162 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA163 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB163 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC163 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA164 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB164 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC164 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA165 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB165 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC165 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA166 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB166 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC166 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA167 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB167 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC167 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA168 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB168 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC168 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA169 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB169 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC169 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA170 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB170 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC170 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA171 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceB171 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC171 : Charge := ![-3, 0, 0, 0, 0, 3]

def sourceA172 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB172 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC172 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA174 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB174 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC174 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA176 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB176 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC176 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA177 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB177 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC177 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA178 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB178 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC178 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA179 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB179 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC179 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA180 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB180 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC180 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA181 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB181 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC181 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA182 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB182 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC182 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA183 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB183 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC183 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA184 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB184 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC184 : Charge := ![3, 0, -1, -2, 0, 0]

def sourceA186 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB186 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC186 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA187 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB187 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC187 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA188 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB188 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC188 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA189 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB189 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC189 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA190 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB190 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC190 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA191 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB191 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC191 : Charge := ![0, 0, 1, 2, -1, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1600 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1600 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1600 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA1601 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1601 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1601 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA1602 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1602 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1602 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1604 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1604 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1604 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1606 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1606 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1606 : Charge := ![2, 1, 0, 0, 0, -3]

def sourceA1607 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1607 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1607 : Charge := ![2, -1, 0, -1, -1, 1]

def sourceA1608 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1608 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1608 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1609 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1609 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1609 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1610 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1610 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1610 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1611 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1611 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1611 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1612 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1612 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1612 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA1613 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1613 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1613 : Charge := ![2, -1, 0, -1, 1, -1]

def sourceA1614 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1614 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1614 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1615 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1615 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1615 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1616 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1616 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1616 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1617 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1617 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1617 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1618 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1618 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1618 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1619 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1619 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1619 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1620 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1620 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1620 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1621 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1621 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1621 : Charge := ![2, -1, 0, -1, 2, -2]

def sourceA1622 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1622 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1622 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA1623 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1623 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1623 : Charge := ![2, -1, 0, 0, 1, -2]

def sourceA1624 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1624 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1624 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1625 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1625 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1625 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1626 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1626 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1626 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1627 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1627 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1627 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1628 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1628 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1628 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA1629 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1629 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1629 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA1630 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1630 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1630 : Charge := ![2, -1, 1, -1, -1, 0]

def sourceA1631 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1631 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1631 : Charge := ![2, -1, 1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1632 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1632 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1632 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1633 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1633 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1633 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1634 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1634 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1634 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1635 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceB1635 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1635 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1636 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1636 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1636 : Charge := ![2, 1, -1, 0, -1, -1]

def sourceA1637 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1637 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceC1637 : Charge := ![2, 1, -1, 0, -1, -1]

def sourceA1638 : Charge := ![2, -1, 1, -1, 0, -1]
def sourceB1638 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC1638 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1639 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1639 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC1639 : Charge := ![2, -1, 1, -1, 1, -2]

def sourceA1640 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1640 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1640 : Charge := ![2, -1, 2, -1, -1, -1]

def sourceA1641 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1641 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC1641 : Charge := ![2, -1, 2, -1, -1, -1]

def sourceA1642 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1642 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC1642 : Charge := ![2, -1, 2, -1, 0, -2]

def sourceA1643 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceB1643 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1643 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1644 : Charge := ![2, 0, 0, -2, -1, 1]
def sourceB1644 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC1644 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1645 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceB1645 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1645 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1646 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceB1646 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC1646 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1647 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1647 : Charge := ![2, 0, 0, 1, -3, 0]
def sourceC1647 : Charge := ![2, 0, 0, -2, 2, -2]

def sourceA1648 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1648 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1648 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1649 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1649 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1649 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1650 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1650 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1650 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1651 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1651 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1652 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1652 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1652 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1653 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1653 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1653 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1654 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1654 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1654 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1655 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB1655 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1655 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1656 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1656 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1656 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1657 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1657 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1657 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1658 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB1658 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1658 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1659 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1659 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1659 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1660 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1660 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1660 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1661 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1661 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1661 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA1662 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1662 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1662 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA1663 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1663 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1663 : Charge := ![2, 0, 0, -1, 1, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1664 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1664 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1664 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA1667 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1667 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1667 : Charge := ![2, 0, 0, -1, 2, -3]

def sourceA1668 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1668 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC1668 : Charge := ![2, 0, 1, -2, 1, -2]

def sourceA1669 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1669 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1669 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1670 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1670 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1670 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1671 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1671 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1671 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1672 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1672 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1672 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1673 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1673 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1673 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1674 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1674 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1674 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA1675 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1675 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1675 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA1677 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1677 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1677 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1678 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1678 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1678 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1679 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1679 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1679 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1680 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1680 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1680 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1681 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1681 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1681 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1682 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1682 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1682 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1683 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1683 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1683 : Charge := ![2, 0, -1, 0, -1, 0]

def sourceA1684 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1684 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1684 : Charge := ![2, 0, -1, 0, -1, 0]

def sourceA1686 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1686 : Charge := ![2, 0, -1, 0, -2, 1]
def sourceC1686 : Charge := ![2, 0, 1, -1, 1, -3]

def sourceA1688 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1688 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC1688 : Charge := ![2, 0, 2, -2, -1, -1]

def sourceA1689 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1689 : Charge := ![2, 0, -2, 1, -1, 0]
def sourceC1689 : Charge := ![2, 0, 2, -2, 0, -2]

def sourceA1690 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1690 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1690 : Charge := ![2, 0, 2, -1, -1, -2]

def sourceA1693 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1693 : Charge := ![2, 0, -2, 0, -1, 1]
def sourceC1693 : Charge := ![2, 0, 2, -1, 0, -3]

def sourceA1695 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1695 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC1695 : Charge := ![2, 1, 1, -2, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1696 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1696 : Charge := ![2, -1, -1, 1, -1, 0]
def sourceC1696 : Charge := ![2, 1, 1, -2, 0, -2]

def sourceA1697 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1697 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1697 : Charge := ![2, 1, 1, -1, -1, -2]

def sourceA1700 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1700 : Charge := ![2, -1, -1, 0, -1, 1]
def sourceC1700 : Charge := ![2, 1, 1, -1, 0, -3]

def sourceA1702 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1702 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1702 : Charge := ![3, -2, 0, -1, -1, 1]

def sourceA1703 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1703 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1703 : Charge := ![3, -2, 0, -1, 1, -1]

def sourceA1704 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1704 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC1704 : Charge := ![3, -2, 0, 0, 1, -2]

def sourceA1706 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1706 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1706 : Charge := ![3, -2, 1, -1, -1, 0]

def sourceA1707 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1707 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceC1707 : Charge := ![3, -2, 1, -1, 0, -1]

def sourceA1708 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1708 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1708 : Charge := ![3, -2, 1, 0, 0, -2]

def sourceA1709 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1709 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1709 : Charge := ![3, -1, -1, -1, -1, 1]

def sourceA1710 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1710 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1710 : Charge := ![3, -1, -1, -1, -1, 1]

def sourceA1711 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1711 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1711 : Charge := ![3, -1, -1, -1, 1, -1]

def sourceA1712 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1712 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC1712 : Charge := ![3, -1, -1, 0, 1, -2]

def sourceA1713 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1713 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1713 : Charge := ![3, -1, 0, -2, -1, 1]

def sourceA1714 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1714 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1714 : Charge := ![3, -1, 0, -2, -1, 1]

def sourceA1715 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1715 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1715 : Charge := ![3, -1, 0, -2, 1, -1]

def sourceA1716 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1716 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1716 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA1717 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1717 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1717 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA1718 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1718 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1718 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA1719 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1719 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1719 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA1720 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1720 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1720 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA1723 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1723 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1723 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1724 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1724 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1724 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1725 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1725 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1725 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1726 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1726 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1726 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1727 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1727 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1727 : Charge := ![3, -1, 0, -1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1728 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1728 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1728 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1729 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1729 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1729 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1730 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1730 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1730 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1732 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1732 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1732 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1733 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1733 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1733 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1734 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1734 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1734 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1735 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1735 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1735 : Charge := ![3, -1, 0, -1, 1, -2]

def sourceA1737 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB1737 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceC1737 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1738 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1738 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1738 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1739 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1739 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1739 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1740 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1740 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1740 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1741 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1741 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1741 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1742 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1742 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1742 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1743 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1743 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1743 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1744 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1744 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1744 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1745 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1745 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1745 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1746 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1746 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1746 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA1747 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1747 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1747 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1748 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1748 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1748 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1749 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1749 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceC1749 : Charge := ![3, -1, 0, 0, 1, -3]

def sourceA1750 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1750 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1750 : Charge := ![3, -1, 1, -2, -1, 0]

def sourceA1751 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1751 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1751 : Charge := ![3, -1, 1, -2, -1, 0]

def sourceA1752 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1752 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1752 : Charge := ![3, -1, 1, -2, 0, -1]

def sourceA1753 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1753 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1753 : Charge := ![3, -1, 1, -1, -1, -1]

def sourceA1756 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1756 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1756 : Charge := ![3, -1, 1, -1, -1, -1]

def sourceA1759 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1759 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1759 : Charge := ![3, -1, 1, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1761 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1761 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1761 : Charge := ![3, -1, 1, -1, 0, -2]

def sourceA1762 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceB1762 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceC1762 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1763 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1763 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1763 : Charge := ![3, -1, 1, 0, 0, -3]

def sourceA1766 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1766 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1766 : Charge := ![3, 0, 0, -3, 1, -1]

def sourceA1769 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1769 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1769 : Charge := ![3, 0, 0, -2, -1, 0]

def sourceA1770 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1770 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC1770 : Charge := ![3, 0, 0, -2, -1, 0]

def sourceA1773 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceB1773 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC1773 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1775 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1775 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1775 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA1776 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1776 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC1776 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA1777 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1777 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1777 : Charge := ![1, 0, 0, 1, -1, -1]

def sourceA1779 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceB1779 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1779 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1780 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1780 : Charge := ![1, 0, 0, 1, -2, 0]
def sourceC1780 : Charge := ![3, 0, 0, -2, 1, -2]

def sourceA1781 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1781 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1781 : Charge := ![3, 0, 0, -1, -1, -1]

def sourceA1782 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1782 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1782 : Charge := ![3, 0, 0, -1, 0, -2]

def sourceA1783 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1783 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC1783 : Charge := ![3, 0, 0, -1, 1, -3]

def sourceA1784 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1784 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1784 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1785 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1785 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1785 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1786 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1786 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1786 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1787 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1787 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1787 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA1788 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1788 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC1788 : Charge := ![3, 0, 0, 0, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1792 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceB1792 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1792 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1793 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1793 : Charge := ![1, 0, -1, 2, 0, -2]
def sourceC1793 : Charge := ![3, 0, 1, -3, -1, 0]

def sourceA1795 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1795 : Charge := ![1, 0, -1, 2, -1, -1]
def sourceC1795 : Charge := ![3, 0, 1, -3, 0, -1]

def sourceA1796 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1796 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1796 : Charge := ![3, 0, 1, -2, -2, 0]

def sourceA1797 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1797 : Charge := ![1, 0, -1, 1, 1, -2]
def sourceC1797 : Charge := ![3, 0, 1, -2, -2, 0]

def sourceA1798 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1798 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1798 : Charge := ![3, 0, 1, -2, -1, -1]

def sourceA1800 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1800 : Charge := ![1, 0, -1, 1, 0, -1]
def sourceC1800 : Charge := ![3, 0, 1, -2, -1, -1]

def sourceA1803 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1803 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1803 : Charge := ![3, 0, 1, -2, 0, -2]

def sourceA1804 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1804 : Charge := ![1, 0, -1, 1, -1, 0]
def sourceC1804 : Charge := ![3, 0, 1, -2, 0, -2]

def sourceA1807 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1807 : Charge := ![1, 0, -1, 0, -1, 1]
def sourceC1807 : Charge := ![3, 0, 1, -1, 0, -3]

def sourceA1809 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1809 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1809 : Charge := ![4, -1, -1, -1, -1, 0]

def sourceA1811 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1811 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1811 : Charge := ![4, -1, -1, -1, -1, 0]

def sourceA1812 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB1812 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceC1812 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1813 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1813 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1813 : Charge := ![4, -1, -1, -1, 0, -1]

def sourceA1814 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1814 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1814 : Charge := ![4, -1, -1, -1, 0, -1]

def sourceA1815 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1815 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1815 : Charge := ![4, -1, 0, -1, -1, -1]

def sourceA1816 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1816 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1816 : Charge := ![4, -1, 0, -1, -1, -1]

def sourceA1817 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1817 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1817 : Charge := ![4, -1, 0, -1, -1, -1]

def sourceA1818 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB1818 : Charge := ![4, -1, 0, -1, -1, -1]
def sourceC1818 : Charge := ![-4, 0, 0, 1, 1, 2]

def sourceA1821 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1821 : Charge := ![4, 0, 0, -1, -1, -2]
def sourceC1821 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1822 : Charge := ![1, 0, -1, -1, -1, 2]
def sourceB1822 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1822 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1823 : Charge := ![1, 0, -1, -1, -1, 2]
def sourceB1823 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC1823 : Charge := ![-4, 0, 1, 1, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1824 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1824 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1824 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA1825 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceB1825 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1825 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1826 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceB1826 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1826 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1827 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1827 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1827 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA1828 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1828 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1828 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1831 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1831 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1831 : Charge := ![2, -1, -1, -1, -1, 2]

def sourceA1832 : Charge := ![2, -1, -1, -1, -1, 2]
def sourceB1832 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1832 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1833 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1833 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceC1833 : Charge := ![2, 1, 0, 0, -1, -2]

def sourceA1834 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1834 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1834 : Charge := ![2, -1, -1, -1, 0, 1]

def sourceA1835 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1835 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1835 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1836 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1836 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1836 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1837 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1837 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1837 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1838 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1838 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1838 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1839 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1839 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1839 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1841 : Charge := ![2, 0, -2, -1, -1, 2]
def sourceB1841 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC1841 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1842 : Charge := ![2, 0, -2, -1, 0, 1]
def sourceB1842 : Charge := ![2, 0, 1, 0, -1, -2]
def sourceC1842 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1843 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1843 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1843 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1844 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1844 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1844 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1845 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1845 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1845 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1846 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1846 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1846 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1847 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1847 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1847 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1848 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1848 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1848 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA1850 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1850 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1850 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1851 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1851 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1851 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1852 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1852 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1852 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1853 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1853 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1853 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1854 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB1854 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1854 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1855 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1855 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC1855 : Charge := ![2, 1, -2, -1, -1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1856 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1856 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1856 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA1857 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1857 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1857 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA1858 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1858 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1858 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA1859 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1859 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1859 : Charge := ![2, 1, -1, -1, -1, 0]

def sourceA1860 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1860 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1860 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA1861 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1861 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1861 : Charge := ![2, -1, 0, 0, 0, -1]

def sourceA1863 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1863 : Charge := ![2, -2, 1, 0, 0, -1]
def sourceC1863 : Charge := ![2, 2, -2, -1, -1, 0]

def sourceA1864 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1864 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1864 : Charge := ![2, 2, -1, -1, -1, -1]

def sourceA1865 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1865 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1865 : Charge := ![2, 2, -1, -1, -1, -1]

def sourceA1867 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1867 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceC1867 : Charge := ![3, -2, -1, -1, 0, 1]

def sourceA1868 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1868 : Charge := ![1, 1, 1, 0, -1, -2]
def sourceC1868 : Charge := ![3, -1, -2, -1, 0, 1]

def sourceA1869 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1869 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1869 : Charge := ![3, -1, -1, -1, -1, 1]

def sourceA1870 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1870 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC1870 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1871 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1871 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1871 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA1872 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1872 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1872 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA1873 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1873 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1873 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA1874 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1874 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1874 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1875 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1875 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1875 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1876 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1876 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1876 : Charge := ![-4, 0, 1, 1, 1, 1]

def sourceA1877 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1877 : Charge := ![1, 0, 2, 0, -1, -2]
def sourceC1877 : Charge := ![3, 0, -3, -1, 0, 1]

def sourceA1878 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1878 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1878 : Charge := ![3, 0, -2, -2, 0, 1]

def sourceA1879 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1879 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC1879 : Charge := ![3, 0, -2, -1, -1, 1]

def sourceA1880 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1880 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1880 : Charge := ![3, 0, -2, -1, 0, 0]

def sourceA1881 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1881 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1881 : Charge := ![3, 0, -2, -1, 0, 0]

def sourceA1884 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1884 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1884 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA1885 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1885 : Charge := ![1, -1, 2, 0, -1, -1]
def sourceC1885 : Charge := ![3, 1, -3, -1, 0, 0]

def sourceA1886 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1886 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1886 : Charge := ![3, 1, -2, -2, 0, 0]

def sourceA1887 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1887 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC1887 : Charge := ![3, 1, -1, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1889 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1889 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1889 : Charge := ![4, -1, -1, -1, -1, 0]

def sourceA1890 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1890 : Charge := ![4, 0, -1, -1, -1, -1]
def sourceC1890 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA1891 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1891 : Charge := ![0, 1, 0, 0, 2, -3]
def sourceC1891 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA1892 : Charge := ![0, 1, 0, 0, 2, -3]
def sourceB1892 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1892 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1893 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1893 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1893 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA1894 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1894 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1894 : Charge := ![3, 0, 0, -1, -2, 0]

def sourceA1895 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1895 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1895 : Charge := ![0, 1, 0, 1, 1, -3]

def sourceA1897 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceB1897 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1897 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1898 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1898 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC1898 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA1899 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1899 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1899 : Charge := ![0, 1, 0, 2, -1, -2]

def sourceA1900 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1900 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1900 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1901 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1901 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1901 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1902 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1902 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1902 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1903 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1903 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1903 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA1904 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1904 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1904 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA1905 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB1905 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1905 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1907 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1907 : Charge := ![0, 1, 1, 1, 0, -3]
def sourceC1907 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA1908 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1908 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1908 : Charge := ![0, 1, 1, 2, -1, -3]

def sourceA1909 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1909 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1909 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA1910 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1910 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1910 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA1911 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1911 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1911 : Charge := ![0, 2, 0, 1, -1, -2]

def sourceA1912 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1912 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1912 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1913 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1913 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1913 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1914 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1914 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC1914 : Charge := ![0, 2, 0, 2, -1, -3]

def sourceA1915 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1915 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1915 : Charge := ![0, 3, 0, 0, -1, -2]

def sourceA1916 : Charge := ![0, 3, 0, 0, -1, -2]
def sourceB1916 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1916 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1917 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1917 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1917 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA1918 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1918 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1918 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1919 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1919 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1919 : Charge := ![-3, -1, 0, 0, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA192 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB192 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC192 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA193 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB193 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC193 : Charge := ![0, 0, 1, 2, -1, -2]

def sourceA197 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB197 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC197 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA198 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB198 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC198 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA199 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB199 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC199 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA200 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB200 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC200 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA201 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB201 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC201 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA203 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB203 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC203 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA205 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB205 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC205 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA206 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB206 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC206 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA207 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB207 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC207 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA208 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB208 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC208 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA209 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB209 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC209 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA210 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB210 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC210 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA211 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB211 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC211 : Charge := ![0, 1, 1, 1, -1, -2]

def sourceA214 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB214 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC214 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA215 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB215 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC215 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA217 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB217 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC217 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA219 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB219 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC219 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA222 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB222 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC222 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA223 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB223 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC223 : Charge := ![2, 1, 0, 0, -3, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1920 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1920 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1920 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA1921 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1921 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1921 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1923 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1923 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1923 : Charge := ![2, 0, 1, 0, -2, -1]

def sourceA1924 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1924 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1924 : Charge := ![2, 0, 1, 0, -2, -1]

def sourceA1925 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1925 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1925 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA1926 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1926 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1926 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1927 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1927 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1927 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1929 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1929 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1929 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1930 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1930 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1930 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1931 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1931 : Charge := ![2, 0, 1, 0, -3, 0]
def sourceC1931 : Charge := ![1, 1, -1, 0, 2, -3]

def sourceA1932 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1932 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1932 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA1933 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1933 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1933 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1934 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1934 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1934 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1935 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1935 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1935 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1936 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1936 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1936 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1937 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1937 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1937 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1938 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1938 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1938 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA1939 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1939 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC1939 : Charge := ![1, 1, -1, 1, 1, -3]

def sourceA1940 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1940 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC1940 : Charge := ![1, 1, -1, 2, -1, -2]

def sourceA1942 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1942 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC1942 : Charge := ![1, 1, -1, 2, 0, -3]

def sourceA1943 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1943 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1943 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1944 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1944 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1944 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA1945 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1945 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1945 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1946 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1946 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1946 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA1947 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1947 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1947 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1948 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1948 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1948 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA1949 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1949 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1949 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1950 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1950 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1950 : Charge := ![2, 0, 0, 0, -2, 0]

def sourceA1951 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1951 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1951 : Charge := ![2, 0, 0, 0, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1952 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1952 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1952 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1953 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1953 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1953 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1954 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1954 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1954 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1955 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1955 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1955 : Charge := ![1, 1, 0, 0, 1, -3]

def sourceA1956 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1956 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1956 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1957 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB1957 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1957 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1958 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1958 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1958 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA1959 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1959 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1959 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1960 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1960 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1960 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA1961 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1961 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1961 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1962 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB1962 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC1962 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1965 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1965 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1965 : Charge := ![1, 1, 0, 1, -1, -2]

def sourceA1966 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1966 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1966 : Charge := ![1, 1, 0, 1, -1, -2]

def sourceA1967 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1967 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1967 : Charge := ![1, 1, 0, 1, -1, -2]

def sourceA1968 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1968 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC1968 : Charge := ![1, 1, 0, 1, -1, -2]

def sourceA1971 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1971 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1971 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA1973 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1973 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1973 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1974 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1974 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1974 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1975 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1975 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1975 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1976 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1976 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1976 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1977 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1977 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1977 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1978 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1978 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1978 : Charge := ![1, 1, 0, 1, 0, -3]

def sourceA1979 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceB1979 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1979 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA1981 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1981 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC1981 : Charge := ![1, 1, 0, 2, -2, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1987 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1987 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1987 : Charge := ![1, 1, 1, 1, -1, -3]

def sourceA1991 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1991 : Charge := ![2, -1, 1, 0, -2, 0]
def sourceC1991 : Charge := ![1, 2, -1, 0, 1, -3]

def sourceA1993 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1993 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1993 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA1996 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1996 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1996 : Charge := ![1, 2, 0, 0, -1, -2]

def sourceA1997 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1997 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1997 : Charge := ![1, 2, 0, 0, -1, -2]

def sourceA1998 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1998 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1998 : Charge := ![2, -1, 0, 0, -1, 0]

def sourceA2000 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2000 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2000 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2001 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2001 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2001 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2002 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2002 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2002 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2003 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2003 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2003 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2008 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2008 : Charge := ![1, 2, 0, 0, -3, 0]
def sourceC2008 : Charge := ![2, -1, 0, 0, 2, -3]

def sourceA2009 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2009 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC2009 : Charge := ![2, -1, 0, 1, 1, -3]

def sourceA2011 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2011 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2011 : Charge := ![2, -1, 0, 2, -1, -2]

def sourceA2012 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2012 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceC2012 : Charge := ![2, -1, 0, 2, 0, -3]

def sourceA2014 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2014 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2014 : Charge := ![2, -1, 1, 1, -1, -2]

def sourceA2015 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2015 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC2015 : Charge := ![2, -1, 1, 1, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2016 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2016 : Charge := ![1, 1, 1, 0, -3, 0]
def sourceC2016 : Charge := ![2, 0, -1, 0, 2, -3]

def sourceA2017 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2017 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC2017 : Charge := ![2, 0, -1, 1, 1, -3]

def sourceA2018 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2018 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2018 : Charge := ![2, 0, -1, 2, -1, -2]

def sourceA2019 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2019 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2019 : Charge := ![2, 0, -1, 2, -1, -2]

def sourceA2020 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2020 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2020 : Charge := ![2, 0, -1, 2, 0, -3]

def sourceA2021 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2021 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2021 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2022 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2022 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2022 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2023 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2023 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2023 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2024 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2024 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2024 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2025 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2025 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2025 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2026 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2026 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2026 : Charge := ![2, 0, 0, 0, 1, -3]

def sourceA2027 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2027 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2027 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2028 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2028 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2028 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2031 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2031 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2031 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA2032 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2032 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2032 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA2033 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2033 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2033 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA2034 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2034 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2034 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA2035 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2035 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2035 : Charge := ![2, 0, 0, 1, -1, -2]

def sourceA2036 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2036 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC2036 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA2039 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2039 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2039 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2040 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2040 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2040 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2041 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2041 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2041 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2042 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2042 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2042 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2043 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2043 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2043 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2044 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2044 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2044 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2045 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2045 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2045 : Charge := ![2, 0, 0, 1, 0, -3]

def sourceA2046 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2046 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2046 : Charge := ![1, 1, 0, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2051 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2051 : Charge := ![1, 1, 0, -2, 1, -1]
def sourceC2051 : Charge := ![2, 0, 0, 2, -2, -2]

def sourceA2052 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2052 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2052 : Charge := ![2, 0, 0, 2, -1, -3]

def sourceA2054 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2054 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2054 : Charge := ![2, 0, 0, 2, -1, -3]

def sourceA2056 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2056 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2056 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA2057 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2057 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2057 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA2059 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2059 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2059 : Charge := ![2, 0, 1, 1, -1, -3]

def sourceA2061 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2061 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2061 : Charge := ![2, 1, -1, 0, 1, -3]

def sourceA2062 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2062 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceC2062 : Charge := ![2, 1, -1, 0, 1, -3]

def sourceA2064 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB2064 : Charge := ![2, 1, -1, 0, 1, -3]
def sourceC2064 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2065 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2065 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2065 : Charge := ![2, 1, -1, 1, -1, -2]

def sourceA2072 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2072 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2072 : Charge := ![2, 1, 0, 0, 0, -3]

def sourceA2073 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2073 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2073 : Charge := ![2, 1, 0, 0, 0, -3]

def sourceA2074 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2074 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2074 : Charge := ![2, 1, 0, 1, -2, -2]

def sourceA2077 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2077 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2077 : Charge := ![2, 1, 0, 1, -2, -2]

def sourceA2079 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2079 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2079 : Charge := ![2, 1, 0, 1, -1, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2084 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceB2084 : Charge := ![2, 2, 0, 0, -1, -3]
def sourceC2084 : Charge := ![-3, -1, 0, 0, 1, 3]

def sourceA2085 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2085 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2085 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2086 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2086 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2086 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2087 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2087 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2087 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2088 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2088 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC2088 : Charge := ![3, 0, 0, 1, -1, -3]

def sourceA2089 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2089 : Charge := ![3, 1, 0, 0, -1, -3]
def sourceC2089 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2091 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2091 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2091 : Charge := ![0, 1, 0, 2, -2, -1]

def sourceA2092 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceB2092 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2092 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2093 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2093 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC2093 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA2094 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2094 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2094 : Charge := ![0, 1, 1, 1, -2, -1]

def sourceA2095 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB2095 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2095 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2097 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2097 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC2097 : Charge := ![0, 1, 1, 2, -2, -2]

def sourceA2098 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2098 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC2098 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA2099 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2099 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2099 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2100 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2100 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2100 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2101 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2101 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2101 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2102 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2102 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC2102 : Charge := ![0, 2, 0, 2, -2, -2]

def sourceA2103 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2103 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2103 : Charge := ![0, 3, 0, 0, -2, -1]

def sourceA2104 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2104 : Charge := ![3, -2, 0, -1, 0, 0]
def sourceC2104 : Charge := ![0, 3, 0, 1, -2, -2]

def sourceA2105 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2105 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC2105 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA2106 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2106 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2106 : Charge := ![1, 0, 0, 2, -2, -1]

def sourceA2108 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2108 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2108 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2110 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2110 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2110 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2111 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2111 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC2111 : Charge := ![2, 1, -1, -1, 0, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2112 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2112 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2112 : Charge := ![1, 0, 1, 1, -2, -1]

def sourceA2114 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2114 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2114 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2115 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2115 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2115 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2118 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2118 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceC2118 : Charge := ![2, 0, 1, 0, 0, -3]

def sourceA2119 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2119 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2119 : Charge := ![1, 1, -1, 0, -2, 1]

def sourceA2120 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceB2120 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2120 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2121 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceB2121 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2121 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2122 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2122 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2122 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2123 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2123 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2123 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2124 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2124 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2124 : Charge := ![1, 1, -1, 1, -2, 0]

def sourceA2125 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2125 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2125 : Charge := ![1, 1, -1, 1, -2, 0]

def sourceA2126 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2126 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2126 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2129 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2129 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2129 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2130 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2130 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2130 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2132 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB2132 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2132 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2133 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB2133 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2133 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2134 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2134 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC2134 : Charge := ![1, 1, -1, 2, -2, -1]

def sourceA2135 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2135 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2135 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2136 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2136 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2136 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2137 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2137 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2137 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2138 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2138 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2138 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2139 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2139 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2139 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2140 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2140 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2140 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2141 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2141 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2141 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2142 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2142 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2142 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2143 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2143 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2143 : Charge := ![1, 1, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2144 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2144 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2144 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2145 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2145 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2145 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2146 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2146 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2146 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2147 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2147 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceC2147 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA2148 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2148 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2148 : Charge := ![1, 1, 0, 1, -3, 0]

def sourceA2149 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceB2149 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2149 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2152 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2152 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2152 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2153 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2153 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2153 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2154 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2154 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2154 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2155 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2155 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2155 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2156 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2156 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2156 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2157 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2157 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2157 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2160 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2160 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2160 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2161 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2161 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC2161 : Charge := ![1, 1, 0, 2, -3, -1]

def sourceA2168 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2168 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceC2168 : Charge := ![2, -1, 1, 0, 0, -2]

def sourceA2169 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2169 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2169 : Charge := ![1, 2, -1, 0, -2, 0]

def sourceA2170 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2170 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2170 : Charge := ![1, 2, -1, 0, -2, 0]

def sourceA2171 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2171 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2171 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2172 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2172 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2172 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2175 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2175 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2175 : Charge := ![1, 2, -1, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2176 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2176 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2176 : Charge := ![1, 2, -1, 0, -1, -1]

def sourceA2177 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2177 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC2177 : Charge := ![1, 2, 0, 0, -3, 0]

def sourceA2180 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2180 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2180 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2181 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2181 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2181 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2182 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2182 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2182 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2189 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2189 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2189 : Charge := ![2, 0, -1, 2, -2, -1]

def sourceA2190 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2190 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2190 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2191 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2191 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2191 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2192 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2192 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2192 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2193 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2193 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2193 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2194 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2194 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2194 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2195 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2195 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2195 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2196 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2196 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2196 : Charge := ![2, 0, 0, 1, -2, -1]

def sourceA2197 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2197 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC2197 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA2203 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2203 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2203 : Charge := ![2, 0, 1, 1, -2, -2]

def sourceA2207 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2207 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2207 : Charge := ![2, 1, -2, 1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2210 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2210 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2210 : Charge := ![2, 1, -1, 0, -2, 0]

def sourceA2211 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2211 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2211 : Charge := ![2, 1, -1, 0, -2, 0]

def sourceA2212 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2212 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2212 : Charge := ![2, 1, -1, 0, -2, 0]

def sourceA2217 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2217 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2217 : Charge := ![2, 1, -1, 0, -1, -1]

def sourceA2218 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2218 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2218 : Charge := ![2, 1, -1, 0, -1, -1]

def sourceA2219 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2219 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2219 : Charge := ![2, 1, -1, 0, -1, -1]

def sourceA2229 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2229 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2229 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA2230 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2230 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2230 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA2235 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2235 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2235 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA2236 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2236 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2236 : Charge := ![2, 1, 0, 0, -2, -1]

def sourceA2238 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2238 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2238 : Charge := ![2, 1, 0, 1, -2, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA224 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB224 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC224 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA225 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB225 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC225 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA226 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB226 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC226 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA227 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB227 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC227 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA228 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB228 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC228 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA229 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB229 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC229 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA230 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB230 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC230 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA231 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB231 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC231 : Charge := ![2, 1, 0, 0, -3, 0]

def sourceA233 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB233 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC233 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA234 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB234 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC234 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA235 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB235 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC235 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA236 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB236 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC236 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA237 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB237 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC237 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA238 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB238 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC238 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA239 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB239 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC239 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA240 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB240 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC240 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA241 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB241 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC241 : Charge := ![1, -1, 0, 0, 2, -2]

def sourceA244 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB244 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC244 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA245 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB245 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC245 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA246 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB246 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC246 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA247 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB247 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC247 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA250 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB250 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC250 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA251 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceB251 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC251 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA253 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB253 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC253 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA254 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB254 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC254 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA255 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB255 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC255 : Charge := ![2, 1, 0, -1, -2, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2244 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2244 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC2244 : Charge := ![2, 2, -1, -1, -2, 0]

def sourceA2245 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2245 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC2245 : Charge := ![2, 2, -1, 0, -2, -1]

def sourceA2249 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2249 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC2249 : Charge := ![2, 2, 0, 0, -2, -2]

def sourceA2251 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2251 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2251 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA2252 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2252 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2252 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA2253 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2253 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2253 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA2254 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2254 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2254 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA2255 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2255 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2255 : Charge := ![3, -1, 0, 0, -2, 0]

def sourceA2256 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2256 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2256 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2257 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2257 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2257 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2259 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2259 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2259 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2260 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2260 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2260 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2261 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2261 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2261 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA2262 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2262 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2262 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA2263 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2263 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2263 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA2264 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2264 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2264 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA2265 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2265 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2265 : Charge := ![3, -1, 0, 0, -1, -1]

def sourceA2266 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2266 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2266 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2267 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2267 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2267 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2268 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2268 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2268 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2269 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2269 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2269 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2271 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2271 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2271 : Charge := ![3, -1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2273 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2273 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2273 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2274 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2274 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2274 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2275 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2275 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2275 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2276 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2276 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2276 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2277 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2277 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2277 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2278 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2278 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2278 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2279 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2279 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2279 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA2283 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2283 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2283 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2284 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2284 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2284 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2285 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2285 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2285 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2286 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2286 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2286 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2287 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2287 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2287 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2288 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2288 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2288 : Charge := ![3, 0, -1, 0, -1, -1]

def sourceA2289 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2289 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2289 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA2291 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2291 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2291 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2295 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2295 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2295 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA2296 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2296 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2296 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA2297 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2297 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2297 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA2298 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2298 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2298 : Charge := ![3, 0, 0, 0, -3, 0]

def sourceA2302 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2302 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2302 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA2303 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2303 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2303 : Charge := ![3, 0, 0, 0, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2304 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2304 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2304 : Charge := ![3, 0, 0, 0, -2, -1]

def sourceA2308 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2308 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceC2308 : Charge := ![3, 1, -1, 0, -2, -1]

def sourceA2310 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceB2310 : Charge := ![3, 1, -1, 0, -2, -1]
def sourceC2310 : Charge := ![-3, -1, 0, 0, 2, 2]

def sourceA2311 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2311 : Charge := ![3, 1, 0, 0, -2, -2]
def sourceC2311 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2312 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2312 : Charge := ![0, 1, 1, -1, 1, -2]
def sourceC2312 : Charge := ![3, 0, -1, 0, -2, 0]

def sourceA2313 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2313 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2313 : Charge := ![0, 1, 1, -1, 1, -2]

def sourceA2315 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2315 : Charge := ![0, 1, 2, -1, -1, -1]
def sourceC2315 : Charge := ![3, 0, -2, 0, 0, -1]

def sourceA2316 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2316 : Charge := ![3, 0, -2, 0, 0, -1]
def sourceC2316 : Charge := ![0, 1, 2, -1, -1, -1]

def sourceA2318 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2318 : Charge := ![3, 0, -2, 0, -1, 0]
def sourceC2318 : Charge := ![0, 1, 2, -1, 0, -2]

def sourceA2319 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2319 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2319 : Charge := ![0, 2, 0, -1, 1, -2]

def sourceA2320 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2320 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2320 : Charge := ![3, -1, -1, 0, 0, -1]

def sourceA2321 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2321 : Charge := ![3, -1, -1, 0, 0, -1]
def sourceC2321 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA2322 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2322 : Charge := ![0, 2, 1, -1, 0, -2]
def sourceC2322 : Charge := ![3, -1, -1, 0, -1, 0]

def sourceA2323 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2323 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC2323 : Charge := ![0, 2, 1, -1, 0, -2]

def sourceA2325 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2325 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2325 : Charge := ![0, 3, 0, -1, -1, -1]

def sourceA2326 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2326 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC2326 : Charge := ![0, 3, 0, -1, 0, -2]

def sourceA2327 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2327 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC2327 : Charge := ![2, 1, -1, 0, -2, 0]

def sourceA2328 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2328 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2328 : Charge := ![1, 0, 1, -1, 1, -2]

def sourceA2330 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2330 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2330 : Charge := ![2, 1, -2, 0, 0, -1]

def sourceA2331 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2331 : Charge := ![2, 1, -2, 0, 0, -1]
def sourceC2331 : Charge := ![1, 0, 2, -1, -1, -1]

def sourceA2333 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2333 : Charge := ![2, 1, -2, 0, -1, 0]
def sourceC2333 : Charge := ![1, 0, 2, -1, 0, -2]

def sourceA2334 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2334 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC2334 : Charge := ![2, 0, 1, 0, 0, -3]

def sourceA2335 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2335 : Charge := ![1, 1, -1, -1, 1, -1]
def sourceC2335 : Charge := ![2, 0, 1, 0, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2336 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2336 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC2336 : Charge := ![2, 0, 1, -1, -2, 0]

def sourceA2337 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2337 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC2337 : Charge := ![1, 1, -1, 0, 1, -2]

def sourceA2338 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2338 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2338 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2339 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2339 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2339 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2340 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2340 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2340 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA2341 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2341 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2341 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA2342 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2342 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2342 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2343 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2343 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2343 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2344 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2344 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2344 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA2345 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2345 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2345 : Charge := ![1, 1, 0, -1, 0, -1]

def sourceA2348 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2348 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2348 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2349 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2349 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2349 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2350 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2350 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2350 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA2351 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2351 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2351 : Charge := ![2, 0, 0, -1, -1, 0]

def sourceA2352 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2352 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2352 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2353 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2353 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2353 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2354 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2354 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2354 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2355 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2355 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2355 : Charge := ![2, 0, -1, 1, 0, -2]

def sourceA2356 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2356 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC2356 : Charge := ![1, 1, 1, -2, -1, 0]

def sourceA2357 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2357 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2357 : Charge := ![2, 0, -1, 1, -1, -1]

def sourceA2358 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2358 : Charge := ![2, 0, -1, 1, -1, -1]
def sourceC2358 : Charge := ![1, 1, 1, -2, 0, -1]

def sourceA2359 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2359 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC2359 : Charge := ![1, 1, 1, -2, 1, -2]

def sourceA2365 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2365 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2365 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2366 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2366 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2366 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2367 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2367 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2367 : Charge := ![1, 1, 1, -1, 0, -2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2368 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2368 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2368 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2370 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2370 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC2370 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA2371 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2371 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC2371 : Charge := ![1, 1, 1, 0, 0, -3]

def sourceA2374 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2374 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2374 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA2375 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2375 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2375 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA2376 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2376 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2376 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2377 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2377 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC2377 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2378 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2378 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC2378 : Charge := ![1, 2, 0, -2, -1, 0]

def sourceA2382 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2382 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2382 : Charge := ![1, 2, 0, -1, -1, -1]

def sourceA2383 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2383 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2383 : Charge := ![1, 2, 0, -1, -1, -1]

def sourceA2386 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2386 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2386 : Charge := ![1, 2, 0, -1, 0, -2]

def sourceA2387 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2387 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2387 : Charge := ![1, 2, 0, -1, 0, -2]

def sourceA2388 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2388 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC2388 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2390 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2390 : Charge := ![1, 2, -2, 0, 0, -1]
def sourceC2390 : Charge := ![2, -1, 2, -1, -1, -1]

def sourceA2391 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2391 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2391 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA2392 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2392 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2392 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA2393 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2393 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2393 : Charge := ![2, 0, 0, -1, 1, -2]

def sourceA2394 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2394 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2394 : Charge := ![1, 1, 0, 0, -2, 0]

def sourceA2397 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2397 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2397 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2398 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2398 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2398 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2399 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2399 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC2399 : Charge := ![2, 0, 1, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2400 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2400 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2400 : Charge := ![1, 1, -1, 0, 0, -1]

def sourceA2402 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2402 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2402 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2403 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2403 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2403 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2404 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2404 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2404 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2405 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2405 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2405 : Charge := ![1, 1, -1, 0, -1, 0]

def sourceA2410 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2410 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2410 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA2411 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2411 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2411 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA2415 : Charge := ![1, 0, 1, 0, -2, 0]
def sourceB2415 : Charge := ![2, 1, -1, -1, 1, -2]
def sourceC2415 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2416 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2416 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2416 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA2417 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2417 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2417 : Charge := ![2, 1, -1, 0, 0, -2]

def sourceA2425 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2425 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2425 : Charge := ![2, 1, 0, 0, 0, -3]

def sourceA2426 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2426 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2426 : Charge := ![2, 1, 0, 0, 0, -3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2439 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2439 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2439 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA2440 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2440 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2440 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA2441 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2441 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2441 : Charge := ![3, -1, 0, -1, -1, 0]

def sourceA2442 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2442 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2442 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2443 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2443 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC2443 : Charge := ![0, 2, 0, 0, 0, -2]

def sourceA2445 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2445 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2445 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA2446 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2446 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2446 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA2447 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2447 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2447 : Charge := ![3, -1, 0, -1, 0, -1]

def sourceA2448 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2448 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2448 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2449 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2449 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2449 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2450 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2450 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2450 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2451 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2451 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2451 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA2452 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2452 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2452 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA2453 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2453 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2453 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA2454 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2454 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2454 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA2455 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2455 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2455 : Charge := ![3, -1, 0, 0, 0, -2]

def sourceA2456 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2456 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2456 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA2457 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2457 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2457 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA2458 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2458 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC2458 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2460 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2460 : Charge := ![0, 2, -1, 0, 0, -1]
def sourceC2460 : Charge := ![3, -1, 1, -1, -1, -1]

def sourceA2461 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2461 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2461 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA2462 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2462 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2462 : Charge := ![3, 0, -1, -1, -1, 0]

def sourceA2463 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2463 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2463 : Charge := ![3, 0, -1, -1, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2464 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2464 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2464 : Charge := ![0, 1, 1, 0, 0, -2]

def sourceA2466 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2466 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2466 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA2467 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2467 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2467 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA2468 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2468 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2468 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA2469 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2469 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2469 : Charge := ![3, 0, -1, -1, 0, -1]

def sourceA2470 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2470 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2470 : Charge := ![0, 1, 1, 0, -1, -1]

def sourceA2471 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2471 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2471 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2472 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2472 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2472 : Charge := ![3, 0, -1, 0, 0, -2]

def sourceA2473 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2473 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2473 : Charge := ![3, 0, -1, 0, 0, -2]

def sourceA2474 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2474 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2474 : Charge := ![3, 0, -1, 0, 0, -2]

def sourceA2475 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2475 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2475 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA2476 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB2476 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2476 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2477 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2477 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2477 : Charge := ![3, 0, 0, -2, -1, 0]

def sourceA2478 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2478 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2478 : Charge := ![3, 0, 0, -2, -1, 0]

def sourceA2479 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2479 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2479 : Charge := ![3, 0, 0, -2, -1, 0]

def sourceA2481 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceB2481 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC2481 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2482 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2482 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2482 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA2483 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2483 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2483 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA2484 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2484 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2484 : Charge := ![3, 0, 0, -2, 0, -1]

def sourceA2485 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2485 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2485 : Charge := ![0, 1, 0, 1, -1, -1]

def sourceA2486 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB2486 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2486 : Charge := ![-3, -1, 0, 1, 1, 2]

def sourceA2487 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2487 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2487 : Charge := ![3, 0, 0, -1, -1, -1]

def sourceA2488 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2488 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2488 : Charge := ![3, 0, 0, -1, 0, -2]

def sourceA2489 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2489 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2489 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2491 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2491 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2491 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2492 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2492 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2492 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2493 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2493 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2493 : Charge := ![3, 0, 0, 0, 0, -3]

def sourceA2494 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2494 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC2494 : Charge := ![3, 0, 1, -1, -1, -2]

def sourceA2495 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceB2495 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC2495 : Charge := ![-3, -1, 0, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2496 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2496 : Charge := ![3, 1, 0, -1, -1, -2]
def sourceC2496 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2497 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2497 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2497 : Charge := ![0, 3, -1, -1, -1, 0]

def sourceA2499 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2499 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2499 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2500 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2500 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2500 : Charge := ![1, 1, -1, -1, 0, 0]

def sourceA2502 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2502 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2502 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA2503 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2503 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2503 : Charge := ![2, 0, -1, -1, -1, 1]

def sourceA2504 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2504 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC2504 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2508 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2508 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2508 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA2509 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2509 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2509 : Charge := ![3, -1, -1, -1, 0, 0]

def sourceA2510 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2510 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC2510 : Charge := ![0, 2, 0, 0, -1, -1]

def sourceA2511 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2511 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC2511 : Charge := ![-3, -1, 1, 1, 1, 1]

def sourceA2512 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2512 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2512 : Charge := ![3, 0, -2, -1, 0, 0]

def sourceA2513 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2513 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2513 : Charge := ![3, 0, -2, -1, 0, 0]

def sourceA2514 : Charge := ![-3, -1, 1, 1, 1, 1]
def sourceB2514 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC2514 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2515 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2515 : Charge := ![-1, 2, 0, 1, -2, 0]
def sourceC2515 : Charge := ![3, 0, 0, -1, 0, -2]

def sourceA2516 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2516 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2516 : Charge := ![-1, 2, 0, 1, -2, 0]

def sourceA2519 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2519 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC2519 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA2520 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2520 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC2520 : Charge := ![2, 1, -1, -1, 0, -1]

def sourceA2521 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2521 : Charge := ![0, 2, -1, 1, -2, 0]
def sourceC2521 : Charge := ![2, 0, 1, -1, 0, -2]

def sourceA2522 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2522 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC2522 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2523 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2523 : Charge := ![0, 2, -1, 1, -1, -1]
def sourceC2523 : Charge := ![2, 0, 1, -1, -1, -1]

def sourceA2524 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2524 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC2524 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2525 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2525 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceC2525 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2526 : Charge := ![0, 2, 0, 0, -2, 0]
def sourceB2526 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2526 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2527 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2527 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2527 : Charge := ![2, 0, 0, 0, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2528 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2528 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2528 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2529 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2529 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2529 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2532 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2532 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2532 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2533 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2533 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2533 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2534 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2534 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2534 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2535 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2535 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2535 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2536 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2536 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2536 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2537 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2537 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2537 : Charge := ![0, 2, 0, 1, -2, -1]

def sourceA2545 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2545 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2545 : Charge := ![0, 3, 0, 0, -2, -1]

def sourceA2546 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2546 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2546 : Charge := ![0, 3, 0, 0, -2, -1]

def sourceA2547 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2547 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2547 : Charge := ![0, 3, 0, 0, -2, -1]

def sourceA2550 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2550 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2550 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2551 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2551 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2551 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2552 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2552 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2552 : Charge := ![-2, -2, 0, 0, 2, 2]

def sourceA2553 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2553 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2553 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2555 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2555 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2555 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2556 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2556 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2556 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2557 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2557 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2557 : Charge := ![1, 1, 0, 1, -2, -1]

def sourceA2558 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2558 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2558 : Charge := ![1, 1, 0, 1, -2, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA256 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB256 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC256 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA257 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB257 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC257 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA258 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB258 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC258 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA259 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB259 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC259 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA260 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB260 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC260 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA261 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB261 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC261 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA262 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB262 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC262 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA263 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB263 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC263 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA264 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB264 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC264 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA265 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB265 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC265 : Charge := ![2, 1, 0, -1, -2, 0]

def sourceA268 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB268 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC268 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA269 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB269 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC269 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA270 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB270 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC270 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA271 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB271 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC271 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA272 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB272 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC272 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA273 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB273 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC273 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA274 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB274 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC274 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA275 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB275 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC275 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA276 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB276 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC276 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA277 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB277 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC277 : Charge := ![1, -1, 0, 1, 1, -2]

def sourceA280 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB280 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC280 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA281 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB281 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC281 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA282 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB282 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC282 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA283 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB283 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC283 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA286 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB286 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC286 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA287 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB287 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC287 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2565 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2565 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2565 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2566 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2566 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2566 : Charge := ![1, 2, 0, 0, -2, -1]

def sourceA2571 : Charge := ![-2, -2, 0, 0, 2, 2]
def sourceB2571 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceC2571 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2572 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2572 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceC2572 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2573 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2573 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2573 : Charge := ![0, 2, 0, -1, -1, 0]

def sourceA2574 : Charge := ![0, 2, 0, -1, -1, 0]
def sourceB2574 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2574 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2575 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2575 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2575 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2576 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceB2576 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2576 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2579 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2579 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2579 : Charge := ![0, 2, 0, -1, 1, -2]

def sourceA2580 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2580 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2580 : Charge := ![0, 2, 0, -1, 1, -2]

def sourceA2582 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2582 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceC2582 : Charge := ![2, 0, -1, 0, 0, -1]

def sourceA2583 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2583 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2583 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA2584 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2584 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2584 : Charge := ![0, 2, 1, -1, -1, -1]

def sourceA2587 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2587 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2587 : Charge := ![0, 2, 1, -1, 0, -2]

def sourceA2588 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2588 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2588 : Charge := ![0, 2, 1, -1, 0, -2]

def sourceA2591 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2591 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2591 : Charge := ![0, 3, 0, -1, -1, -1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2592 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2592 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2592 : Charge := ![0, 3, 0, -1, -1, -1]

def sourceA2595 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2595 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2595 : Charge := ![0, 3, 0, -1, 0, -2]

def sourceA2596 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2596 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2596 : Charge := ![0, 3, 0, -1, 0, -2]

def sourceA2597 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2597 : Charge := ![1, 1, 0, 0, 0, -2]

def sourceA2598 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2598 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2598 : Charge := ![1, 1, 0, -1, -1, 0]

def sourceA2599 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2599 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2599 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2602 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2602 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2602 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2603 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2603 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2603 : Charge := ![1, 1, 0, -1, 1, -2]

def sourceA2607 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2607 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2607 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2608 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2608 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2608 : Charge := ![1, 1, 1, -1, 0, -2]

def sourceA2611 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2611 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2611 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA2612 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2612 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2612 : Charge := ![1, 2, -1, -1, -1, 0]

def sourceA2614 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2614 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2614 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA2615 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2615 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2615 : Charge := ![1, 2, -1, -1, 0, -1]

def sourceA2618 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2618 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2618 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2619 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2619 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2619 : Charge := ![1, 2, -1, 0, 0, -2]

def sourceA2621 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2621 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2621 : Charge := ![1, 2, 0, -2, -1, 0]

def sourceA2622 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2622 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2622 : Charge := ![1, 2, 0, -2, -1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2624 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2624 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2624 : Charge := ![1, 2, 0, -2, 0, -1]

def sourceA2625 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2625 : Charge := ![1, 0, 0, 1, -1, -1]
def sourceC2625 : Charge := ![1, 2, 0, -2, 0, -1]

def sourceA2627 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2627 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2627 : Charge := ![1, 2, 0, -1, -1, -1]

def sourceA2628 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2628 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC2628 : Charge := ![1, 2, 0, -1, 0, -2]

def sourceA2629 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2629 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2630 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC2630 : Charge := ![1, 2, 0, 0, 0, -3]

def sourceA2632 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2632 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceC2632 : Charge := ![1, 2, 1, -1, -1, -2]

def sourceA2633 : Charge := ![1, 0, -1, 0, 0, 0]
def sourceB2633 : Charge := ![1, 2, 1, -1, -1, -2]
def sourceC2633 : Charge := ![-2, -2, 0, 1, 1, 2]

def sourceA2638 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2638 : Charge := ![2, 2, 0, -1, -1, -2]
def sourceC2638 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2639 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2639 : Charge := ![0, 2, -1, -1, -1, 1]
def sourceC2639 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2640 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2640 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2640 : Charge := ![0, 2, -1, -1, -1, 1]

def sourceA2641 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2641 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2641 : Charge := ![0, 2, -1, -1, -1, 1]

def sourceA2642 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2642 : Charge := ![0, 2, -1, -1, 0, 0]
def sourceC2642 : Charge := ![2, 0, 0, 0, -1, -1]

def sourceA2644 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2644 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2644 : Charge := ![0, 3, -1, -1, -1, 0]

def sourceA2645 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2645 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2645 : Charge := ![0, 3, -1, -1, -1, 0]

def sourceA2647 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2647 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2647 : Charge := ![1, 1, 0, 0, -1, -1]

def sourceA2649 : Charge := ![-2, -2, 1, 1, 1, 1]
def sourceB2649 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC2649 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2650 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2650 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2650 : Charge := ![2, 0, 0, 0, 0, -2]

def sourceA2651 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2651 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2651 : Charge := ![0, 1, 1, -1, -1, 0]

def sourceA2652 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2652 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2652 : Charge := ![0, 1, 1, -1, 1, -2]

def sourceA2653 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2653 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2653 : Charge := ![0, 1, 1, -1, 1, -2]

def sourceA2654 : Charge := ![-2, -1, -1, 1, 1, 2]
def sourceB2654 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceC2654 : Charge := ![0, 0, 0, 0, 0, 0]

def sourceA2655 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2655 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2655 : Charge := ![-5, 0, 0, 0, 0, 5]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2656 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2656 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2656 : Charge := ![-5, 0, 0, 0, 0, 5]

def sourceA2657 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2657 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2657 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2658 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2658 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2658 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2659 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2659 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2659 : Charge := ![-5, 0, 0, 0, 1, 4]

def sourceA2663 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2663 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2663 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2664 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2664 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2664 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2665 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2665 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2665 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2667 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2667 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2667 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2669 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2669 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2669 : Charge := ![-5, 0, 0, 0, 2, 3]

def sourceA2671 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2671 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2671 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2672 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2672 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2672 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2673 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2673 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2673 : Charge := ![-5, 0, 0, 1, 1, 3]

def sourceA2679 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2679 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2679 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2680 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2680 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2680 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2681 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2681 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2681 : Charge := ![-5, 0, 0, 1, 2, 2]

def sourceA2687 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2687 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2687 : Charge := ![-5, 0, 1, 1, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2688 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceB2688 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2688 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2689 : Charge := ![2, 0, -1, 0, 1, -2]
def sourceB2689 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2689 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2691 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2691 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2691 : Charge := ![-5, 0, 1, 1, 1, 2]

def sourceA2696 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB2696 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2696 : Charge := ![-5, 1, 1, 1, 1, 1]

def sourceA2697 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2697 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC2697 : Charge := ![-5, 1, 1, 1, 1, 1]

def sourceA2699 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2699 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2699 : Charge := ![-4, -1, 0, 0, 1, 4]

def sourceA2700 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2700 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2700 : Charge := ![-4, -1, 0, 0, 1, 4]

def sourceA2703 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2703 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2703 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2704 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2704 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2704 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2705 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2705 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2705 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2706 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2706 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2706 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2707 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2707 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2707 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2708 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2708 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2708 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2710 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2710 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2710 : Charge := ![-4, -1, 0, 0, 2, 3]

def sourceA2712 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2712 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC2712 : Charge := ![-4, -1, 0, 0, 2, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2720 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2720 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2720 : Charge := ![-4, -1, 0, 1, 1, 3]

def sourceA2725 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2725 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2725 : Charge := ![-4, -1, 0, 1, 2, 2]

def sourceA2726 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2726 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2726 : Charge := ![-4, -1, 0, 1, 2, 2]

def sourceA2728 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2728 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2728 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2729 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2729 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2729 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2730 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB2730 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2730 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2731 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2731 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2731 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2732 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2732 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2732 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2733 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2733 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC2733 : Charge := ![-3, -2, 0, 0, 2, 3]

def sourceA2740 : Charge := ![0, 2, 0, -1, 1, -2]
def sourceB2740 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2740 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2741 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceB2741 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2741 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2742 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2742 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2742 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2743 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2743 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2743 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2744 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2744 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC2744 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2745 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2745 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC2745 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2747 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB2747 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2747 : Charge := ![-3, -2, 0, 1, 1, 3]

def sourceA2748 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceB2748 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2748 : Charge := ![-3, -2, 0, 1, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2756 : Charge := ![0, 2, 0, -1, -2, 1]
def sourceB2756 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2756 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2757 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2757 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2757 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2758 : Charge := ![0, 2, 1, -1, -1, -1]
def sourceB2758 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2758 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2759 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceB2759 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2759 : Charge := ![-3, -2, 0, 1, 2, 2]

def sourceA2766 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2766 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2766 : Charge := ![-3, -1, -1, 1, 1, 3]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA288 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB288 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC288 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA289 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB289 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC289 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA291 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB291 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC291 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA292 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB292 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC292 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA293 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB293 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC293 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA294 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB294 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC294 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA295 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB295 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC295 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA296 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB296 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC296 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA297 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB297 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC297 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA298 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB298 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC298 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA299 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB299 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC299 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA300 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB300 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC300 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA301 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB301 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC301 : Charge := ![2, 1, 0, -2, 0, -1]

def sourceA303 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB303 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC303 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA305 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB305 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC305 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA306 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB306 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC306 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA307 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB307 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC307 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA308 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB308 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC308 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA309 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB309 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC309 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA310 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB310 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC310 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA311 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB311 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC311 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA312 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB312 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC312 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA313 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB313 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC313 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA314 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB314 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC314 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA315 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB315 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC315 : Charge := ![1, -1, 0, 2, -1, -1]

def sourceA316 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB316 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC316 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA317 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB317 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC317 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA318 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB318 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC318 : Charge := ![-3, 0, 0, 0, 1, 2]

def sourceA319 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB319 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC319 : Charge := ![-3, 0, 0, 0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged0 : Integer.Sparse (Fin 271) := [(0, 138332760), (1, 8501053680), (2, -2890080960), (3, -23120647680), (4, -11560323840), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -8670242880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

def pairMerged1 : Integer.Sparse (Fin 271) := [(0, -528840840), (1, -4101114320), (2, -1036820960), (3, -17190215680), (4, 300540160), (5, 5080523400), (6, -499592880), (7, -5780161920), (8, -2890080960), (12, -5705026880), (23, 4335121440), (24, 8670242880), (27, -5995114560)]

def pairMerged2 : Integer.Sparse (Fin 271) := [(0, 1714328), (1, -402065650), (2, -2209009090), (3, 23263569280), (4, 8328009920), (5, 1238915520), (7, -1651887360), (8, -8259436800), (12, 14935559360), (13, 7467779680), (24, 4955662080), (29, 9911324160)]

def pairMerged10 : Integer.Sparse (Fin 271) := [(0, 425465220), (1, -8119256040), (2, 1356329580), (3, 19540684800), (4, 13543423200), (12, 8303453280), (18, 4932865440), (21, 1596594240), (22, 1596594240), (25, -3288576960), (30, -4352973120)]

def pairMerged11 : Integer.Sparse (Fin 271) := [(0, 527992500), (1, -10658200920), (2, 1757390460), (3, 22274745600), (4, 16496778720), (12, 8731124640), (15, -328942080), (17, 1394798400), (18, 4932865440), (19, 1559269440), (20, 1559269440), (21, 1596594240), (22, 3155863680), (23, 164471040), (24, -2489135040), (25, -2959634880), (27, 348699600), (29, -464932800), (30, -6103056960)]

def pairMerged12 : Integer.Sparse (Fin 271) := [(0, -51436332), (1, -1751623200), (2, 798915720), (3, 13752497280), (4, 4638792480), (12, 5389620000), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 2820124800), (24, -411137280), (25, 4155768000), (27, -538860060), (29, 1901892960), (30, 2397677760)]

def pairMerged13 : Integer.Sparse (Fin 271) := [(0, -1686539584), (1, 26393763270), (2, -9222802470), (3, -48954134400), (4, -35572405920), (5, 6319438920), (6, -499592880), (7, -7432049280), (8, -11149517760), (12, -5320084320), (13, 7467779680), (14, -1074388320), (15, -2406939840), (16, 676535760), (17, -1549683360), (18, 3349956960), (19, 1559269440), (20, -2596726080), (21, 1596594240), (22, -9953280), (23, 7155246240), (24, 13214767680), (25, 9605207520), (26, -12674317440), (27, -6533974620), (29, 11813217120), (30, 18622872000)]

def pairMerged14 : Integer.Sparse (Fin 271) := [(0, -109408634), (1, 1684676680), (2, -2029825900), (3, -9843319200), (4, -1933827360), (5, 2142154040), (6, -123585810), (7, -3954745920), (8, -3954745920), (12, -3911200320), (13, -2636497280), (17, 48988800), (23, -16329600), (27, 12247200), (28, 97977600), (29, -81648000), (34, -1318248640), (50, 5932118880), (51, -1977372960)]

def pairMerged15 : Integer.Sparse (Fin 271) := [(0, 8099576), (1, -56641740), (2, 606072000), (3, 624640320), (4, -276472320), (5, -1541099280), (6, 177490980), (7, 831135360), (8, 1662270720), (12, -484685760), (13, -323123840), (26, -276472320), (34, 346449600), (51, 1662270720), (54, 1454057280)]

def pairMerged16 : Integer.Sparse (Fin 271) := [(0, -101309058), (1, 1628034940), (2, -1423753900), (3, -9218678880), (4, -2210299680), (5, 601054760), (6, 53905170), (7, -3123610560), (8, -2292475200), (12, -4395886080), (13, -2959621120), (17, 48988800), (23, -16329600), (26, -276472320), (27, 12247200), (28, 97977600), (29, -81648000), (34, -971799040), (50, 5932118880), (51, -315102240), (54, 1454057280)]

def pairMerged17 : Integer.Sparse (Fin 271) := [(0, 440260440), (1, -9120956850), (2, 3598850490), (3, 34429673760), (4, 10265991360), (5, -7146635880), (6, 771328020), (7, 8709548640), (8, 9228362880), (12, 2075256960), (13, 6744585120), (26, 10265991360), (34, 5324316000), (51, 2075256960), (53, -1556442720), (55, -3112885440)]

def pairMerged18 : Integer.Sparse (Fin 271) := [(0, -32241928), (1, 1069918200), (2, -85892640), (3, -7259368320), (5, 78413040), (7, -1254608640), (12, -3943336320), (13, -7379041920), (23, 2822869440), (25, 2822869440), (31, -458094080), (34, -627304320), (53, 1881912960)]

def pairMerged19 : Integer.Sparse (Fin 271) := [(0, 408018512), (1, -8051038650), (2, 3512957850), (3, 27170305440), (4, 10265991360), (5, -7068222840), (6, 771328020), (7, 7454940000), (8, 9228362880), (12, -1868079360), (13, -634456800), (23, 2822869440), (25, 2822869440), (26, 10265991360), (31, -458094080), (34, 4697011680), (51, 2075256960), (53, 325470240), (55, -3112885440)]

def pairMerged20 : Integer.Sparse (Fin 271) := [(0, 306709454), (1, -6423003710), (2, 2089203950), (3, 17951626560), (4, 8055691680), (5, -6467168080), (6, 825233190), (7, 4331329440), (8, 6935887680), (12, -6263965440), (13, -3594077920), (17, 48988800), (23, 2806539840), (25, 2822869440), (26, 9989519040), (27, 12247200), (28, 97977600), (29, -81648000), (31, -458094080), (34, 3725212640), (50, 5932118880), (51, 1760154720), (53, 325470240), (54, 1454057280), (55, -3112885440)]

def pairMerged21 : Integer.Sparse (Fin 271) := [(0, 564230340), (1, -9199501680), (2, 2247190020), (3, 22750199040), (4, 14786640000), (12, 6329693280), (13, 1348746240), (25, -6381760320), (26, 4487559360), (30, -12763520640), (32, -7393320000), (33, 674373120)]

def pairMerged22 : Integer.Sparse (Fin 271) := [(0, 1067875890), (1, -13625816460), (2, 4109578350), (3, 34682576640), (4, 22843653120), (5, -104274240), (7, 104274240), (8, 417096960), (12, 14764377600), (13, 3534683040), (23, -312822720), (25, -7887143520), (27, 234617040), (29, -625645440), (30, -18804015360), (32, -6685102080), (44, 1876936320), (49, 4544592480), (50, -625645440), (53, -312822720)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged100 : Integer.Sparse (Fin 271) := [(0, -113196), (1, -8511240), (2, 6311340), (3, 94410240), (4, 22360320), (5, -2484480), (7, 14906880), (12, 57143040), (13, 14906880), (14, 110341440), (15, 67080960), (23, -189682560), (24, -22360320), (25, -118281600), (27, 13043520), (32, -44720640), (34, 4968960), (50, -44720640), (53, -44720640), (62, -88467840), (66, 4928400), (111, -71400960), (113, -7453440), (116, 73560960), (124, 44720640), (130, -39427200), (136, 67080960), (144, 110341440)]

def pairMerged101 : Integer.Sparse (Fin 271) := [(0, 9931392), (1, -37706400), (2, 30818880), (5, -14739840), (6, 3684960), (17, 534988800), (23, -356659200), (25, -773729280), (27, 59927040), (29, -178813440), (30, -715737600), (62, -119854080), (66, 14739840), (85, 530634240), (97, 4354560), (100, 534988800), (110, -532085760), (111, -176878080), (130, -117918720), (134, 530634240), (140, 353756160), (142, -176878080), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged102 : Integer.Sparse (Fin 271) := [(0, 9818196), (1, -46217640), (2, 37130220), (3, 94410240), (4, 22360320), (5, -17224320), (6, 3684960), (7, 14906880), (12, 57143040), (13, 14906880), (14, 110341440), (15, 67080960), (17, 534988800), (23, -546341760), (24, -22360320), (25, -892010880), (27, 72970560), (29, -178813440), (30, -715737600), (32, -44720640), (34, 4968960), (50, -44720640), (53, -44720640), (62, -208321920), (66, 19668240), (85, 530634240), (97, 4354560), (100, 534988800), (110, -532085760), (111, -248279040), (113, -7453440), (116, 73560960), (124, 44720640), (130, -157345920), (134, 530634240), (136, 67080960), (140, 353756160), (142, -176878080), (144, 110341440), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged103 : Integer.Sparse (Fin 271) := [(0, 9631404), (1, -153138180), (2, 16920840), (3, 501474240), (4, 300867840), (5, 4687680), (7, -17118720), (12, 101933760), (13, -141854400), (16, -88050240), (18, 198132480), (23, -14688000), (24, -132088320), (25, -132088320), (26, 161441280), (27, 2160), (30, -132088320), (32, -132088320), (34, 1632000), (37, -176100480), (42, 396264960), (46, 198132480), (50, 95385600), (53, 117400320), (54, -73388160), (62, -44029440), (66, -2445840), (111, 29350080), (112, 9783360), (120, -88050240), (121, -58700160), (123, 132088320), (130, 19566720)]

def pairMerged104 : Integer.Sparse (Fin 271) := [(0, -25186536), (1, 338867640), (2, -48609360), (3, -1026794880), (4, -778947840), (5, 11910240), (7, -70813440), (12, -177033600), (13, -47208960), (14, -108164160), (17, -216328320), (23, 404732160), (24, 212440320), (25, 819538560), (26, -354067200), (27, -83479680), (29, 72109440), (30, 747429120), (34, -82615680), (43, -637320960), (54, 318660480), (62, 94849920), (100, -534988800), (110, 178329600), (111, 48072960), (116, -72109440), (134, -432656640), (144, -216328320)]

def pairMerged105 : Integer.Sparse (Fin 271) := [(0, -15555132), (1, 185729460), (2, -31688520), (3, -525320640), (4, -478080000), (5, 16597920), (7, -87932160), (12, -75099840), (13, -189063360), (14, -108164160), (16, -88050240), (17, -216328320), (18, 198132480), (23, 390044160), (24, 80352000), (25, 687450240), (26, -192625920), (27, -83477520), (29, 72109440), (30, 615340800), (32, -132088320), (34, -80983680), (37, -176100480), (42, 396264960), (43, -637320960), (46, 198132480), (50, 95385600), (53, 117400320), (54, 245272320), (62, 50820480), (66, -2445840), (100, -534988800), (110, 178329600), (111, 77423040), (112, 9783360), (116, -72109440), (120, -88050240), (121, -58700160), (123, 132088320), (130, 19566720), (134, -432656640), (144, -216328320)]

def pairMerged106 : Integer.Sparse (Fin 271) := [(0, -5736936), (1, 139511820), (2, 5441700), (3, -430910400), (4, -455719680), (5, -626400), (6, 3684960), (7, -73025280), (12, -17956800), (13, -174156480), (14, 2177280), (15, 67080960), (16, -88050240), (17, 318660480), (18, 198132480), (23, -156297600), (24, 57991680), (25, -204560640), (26, -192625920), (27, -10506960), (29, -106704000), (30, -100396800), (32, -176808960), (34, -76014720), (37, -176100480), (42, 396264960), (43, -637320960), (46, 198132480), (50, 50664960), (53, 72679680), (54, 245272320), (62, -157501440), (66, 17222400), (85, 530634240), (97, 4354560), (110, -353756160), (111, -170856000), (112, 9783360), (113, -7453440), (116, 1451520), (120, -88050240), (121, -58700160), (123, 132088320), (124, 44720640), (130, -137779200), (134, 97977600), (136, 67080960), (140, 353756160), (142, -176878080), (144, -105986880), (145, 2903040), (146, -58959360), (147, -178329600)]

def pairMerged107 : Integer.Sparse (Fin 271) := [(0, 91366470), (1, 217527110), (2, -1047451520), (3, -11539300320), (4, 170845440), (5, 989120680), (6, -44193300), (7, -2873319360), (8, -1370844960), (10, 1364895360), (12, -6704383680), (13, -6646953920), (14, 2177280), (15, 67080960), (16, -88050240), (17, 318660480), (18, 198132480), (23, 468493920), (24, 143488800), (25, -437892480), (26, -1250987520), (27, -151084800), (29, 87134400), (30, -3454591680), (32, 3362918400), (34, -2021673920), (35, -561669120), (36, -1915228800), (37, -164764800), (38, -2465562240), (39, -2465562240), (40, -2729790720), (42, 396264960), (43, -637320960), (45, 2942766720), (46, 933824160), (47, -1189797120), (50, 1477867680), (51, -1424732160), (53, 1548996480), (54, 2303608320), (55, -559454400), (58, 1819860480), (62, -308776320), (66, -17318400), (71, -1364895360), (72, -1364895360), (73, -1364895360), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -31034880), (86, 11335680), (88, -2058445440), (89, 1807056000), (92, -2941263360), (94, -1364895360), (95, -1364895360), (96, 5667840), (97, -1694502720), (98, 1471383360), (99, 671345280), (110, -353756160), (111, 36388800), (112, 9783360), (113, -7453440), (116, 1451520), (120, -88050240), (121, -58700160), (123, 132088320), (124, 44720640), (130, -68697600), (133, 454965120), (134, 97977600), (136, 67080960), (140, 353756160), (142, -176878080), (143, 368778240), (144, -105986880), (145, 2903040), (146, 355530240), (147, -405241920), (148, -335672640)]

def pairMerged108 : Integer.Sparse (Fin 271) := [(0, -6041016), (1, 18245160), (2, -18884880), (3, 133294080), (4, -224640), (5, 6128640), (12, 68296320), (13, 61923840), (15, -110315520), (16, 88050240), (17, 176100480), (20, -220631040), (23, -51278400), (24, 110315520), (26, 39133440), (27, -45964800), (29, 73543680), (34, 19566720), (37, 88050240), (39, 176100480), (50, 14843520), (51, -4947840), (54, -146750400), (112, -39133440), (113, 49029120), (120, 176100480), (121, 58700160), (124, -73543680), (126, 352200960), (136, -220631040), (138, -441262080)]

def pairMerged109 : Integer.Sparse (Fin 271) := [(0, 877068), (1, -40829400), (2, 17212500), (3, 325054080), (4, 100016640), (5, 421200), (6, -1224720), (7, 50008320), (12, 175029120), (15, 225037440), (17, -88179840), (23, -233150400), (24, -225037440), (25, -148340160), (27, 19517760), (28, -176359680), (29, 146966400), (30, 58786560), (32, -75012480), (47, 225037440), (50, -75012480), (54, -150024960), (66, 9376560), (111, -75012480), (113, -75012480), (117, 225037440), (131, -75012480), (134, -176359680), (136, 225037440), (140, -58786560), (144, 112518720), (146, 39191040), (150, -352719360)]

def pairMerged110 : Integer.Sparse (Fin 271) := [(0, -5163948), (1, -22584240), (2, -1672380), (3, 458348160), (4, 99792000), (5, 6549840), (6, -1224720), (7, 50008320), (12, 243325440), (13, 61923840), (15, 114721920), (16, 88050240), (17, 87920640), (20, -220631040), (23, -284428800), (24, -114721920), (25, -148340160), (26, 39133440), (27, -26447040), (28, -176359680), (29, 220510080), (30, 58786560), (32, -75012480), (34, 19566720), (37, 88050240), (39, 176100480), (47, 225037440), (50, -60168960), (51, -4947840), (54, -296775360), (66, 9376560), (111, -75012480), (112, -39133440), (113, -25983360), (117, 225037440), (120, 176100480), (121, 58700160), (124, -73543680), (126, 352200960), (131, -75012480), (134, -176359680), (136, 4406400), (138, -441262080), (140, -58786560), (144, 112518720), (146, 39191040), (150, -352719360)]

def pairMerged111 : Integer.Sparse (Fin 271) := [(0, 1652724), (1, -7054020), (2, -2395440), (3, 79462080), (4, 65543040), (5, 4920480), (7, -16796160), (12, 115421760), (13, -6903360), (16, -38024640), (23, 118091520), (24, 101399040), (25, -187038720), (26, 56678400), (27, -28518480), (32, -102021120), (37, 51010560), (42, 204042240), (46, -152098560), (49, 51010560), (50, 50699520), (53, -17003520), (54, 101399040), (63, -34007040), (66, -3168720), (101, 102021120), (111, 12674880), (112, 38024640), (113, 25349760), (120, -114073920), (136, -76049280)]

def pairMerged112 : Integer.Sparse (Fin 271) := [(0, -9077328), (1, 213979680), (2, -47004480), (3, -1010188800), (4, -454452480), (5, 12326400), (6, -418320), (7, -47520000), (8, -13386240), (12, -358963200), (13, -82321920), (18, -164643840), (21, -120476160), (23, 177361920), (24, 244961280), (25, 102401280), (26, -78531840), (27, -50699520), (30, 140555520), (32, 95040000), (34, -31680000), (42, -60238080), (46, -285120000), (47, -142560000), (49, -246965760), (50, 268392960), (51, -20079360), (53, 40158720), (54, 219525120), (55, 100396800), (89, -60238080), (103, -82321920), (127, -164643840), (129, -120476160), (139, -120476160), (148, 20079360)]

def pairMerged113 : Integer.Sparse (Fin 271) := [(0, -7424604), (1, 206925660), (2, -49399920), (3, -930726720), (4, -388909440), (5, 17246880), (6, -418320), (7, -64316160), (8, -13386240), (12, -243541440), (13, -89225280), (16, -38024640), (18, -164643840), (21, -120476160), (23, 295453440), (24, 346360320), (25, -84637440), (26, -21853440), (27, -79218000), (30, 140555520), (32, -6981120), (34, -31680000), (37, 51010560), (42, 143804160), (46, -437218560), (47, -142560000), (49, -195955200), (50, 319092480), (51, -20079360), (53, 23155200), (54, 320924160), (55, 100396800), (63, -34007040), (66, -3168720), (89, -60238080), (101, 102021120), (103, -82321920), (111, 12674880), (112, 38024640), (113, 25349760), (120, -114073920), (127, -164643840), (129, -120476160), (136, -76049280), (139, -120476160), (148, 20079360)]

def pairMerged114 : Integer.Sparse (Fin 271) := [(0, -12588552), (1, 184341420), (2, -51072300), (3, -472378560), (4, -289117440), (5, 23796720), (6, -1643040), (7, -14307840), (8, -13386240), (12, -216000), (13, -27301440), (15, 114721920), (16, 50025600), (17, 87920640), (18, -164643840), (20, -220631040), (21, -120476160), (23, 11024640), (24, 231638400), (25, -232977600), (26, 17280000), (27, -105665040), (28, -176359680), (29, 220510080), (30, 199342080), (32, -81993600), (34, -12113280), (37, 139060800), (39, 176100480), (42, 143804160), (46, -437218560), (47, 82477440), (49, -195955200), (50, 258923520), (51, -25027200), (53, 23155200), (54, 24148800), (55, 100396800), (63, -34007040), (66, 6207840), (89, -60238080), (101, 102021120), (103, -82321920), (111, -62337600), (112, -1108800), (113, -633600), (117, 225037440), (120, 62026560), (121, 58700160), (124, -73543680), (126, 352200960), (127, -164643840), (129, -120476160), (131, -75012480), (134, -176359680), (136, -71642880), (138, -441262080), (139, -120476160), (140, -58786560), (144, 112518720), (146, 39191040), (148, 20079360), (150, -352719360)]

def pairMerged115 : Integer.Sparse (Fin 271) := [(0, 11596032), (1, -110172960), (2, 35157600), (3, 438174720), (4, 251089920), (12, 2027520), (13, 121236480), (25, 110039040), (26, 125268480), (30, -250076160), (32, -84188160), (33, 64926720), (40, -41264640), (41, 166717440), (42, -165058560), (43, 166717440), (44, 166717440), (49, -82529280), (104, -41264640), (105, 83358720), (106, -82529280), (107, 166717440), (108, 166717440)]

def pairMerged116 : Integer.Sparse (Fin 271) := [(0, 1069056), (1, -18443520), (2, 5333760), (3, 67092480), (4, 32256000), (5, -414720), (7, 1658880), (8, 1105920), (12, 24698880), (13, 12165120), (22, 9953280), (25, -26542080), (26, 10690560), (30, -39813120), (32, -22118400), (33, 2949120), (34, 1105920), (37, 6635520), (38, 13271040), (42, 23224320), (45, 23224320), (46, 4976640), (48, 9953280), (49, 13271040), (50, -11612160), (53, -6635520), (55, -1658880), (63, -6635520), (89, 4976640), (99, 9953280), (101, 6635520), (102, 13271040), (105, 6635520), (106, 13271040), (135, 9953280), (148, -4976640)]

def pairMerged117 : Integer.Sparse (Fin 271) := [(0, 12665088), (1, -128616480), (2, 40491360), (3, 505267200), (4, 283345920), (5, -414720), (7, 1658880), (8, 1105920), (12, 26726400), (13, 133401600), (22, 9953280), (25, 83496960), (26, 135959040), (30, -289889280), (32, -106306560), (33, 67875840), (34, 1105920), (37, 6635520), (38, 13271040), (40, -41264640), (41, 166717440), (42, -141834240), (43, 166717440), (44, 166717440), (45, 23224320), (46, 4976640), (48, 9953280), (49, -69258240), (50, -11612160), (53, -6635520), (55, -1658880), (63, -6635520), (89, 4976640), (99, 9953280), (101, 6635520), (102, 13271040), (104, -41264640), (105, 89994240), (106, -69258240), (107, 166717440), (108, 166717440), (135, 9953280), (148, -4976640)]

def pairMerged118 : Integer.Sparse (Fin 271) := [(0, 9253872), (1, -121031280), (2, 46465920), (3, 410538240), (4, 223672320), (5, -4847040), (7, 7050240), (8, 14100480), (12, 138827520), (13, 33765120), (15, 31726080), (23, -15863040), (24, -31726080), (25, -55365120), (26, 53222400), (27, 7931520), (30, -179159040), (32, -75686400), (33, 7603200), (38, 63452160), (41, 63452160), (42, 68428800), (44, 136857600), (45, 136857600), (49, 34214400), (50, -63452160), (54, -21150720), (55, -52876800), (63, -10575360), (66, 1321920), (89, 31726080), (101, 31726080), (105, 68428800), (106, 68428800), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (124, 31726080), (125, 31726080), (131, -10575360), (148, -10575360)]

def pairMerged119 : Integer.Sparse (Fin 271) := [(0, 6964272), (1, -43651440), (2, -35940240), (3, -85881600), (4, 178859520), (5, 7499520), (6, -458640), (7, 5402880), (8, -14676480), (12, -99429120), (13, -315544320), (18, -132088320), (21, 120476160), (23, -78382080), (24, -76446720), (25, -110799360), (26, 137975040), (27, -1451520), (30, 35562240), (32, 179988480), (34, -8628480), (37, -66044160), (38, -132088320), (41, -396264960), (42, 180714240), (43, 361428480), (46, -5806080), (47, 120476160), (50, 200067840), (51, -22014720), (53, 66044160), (54, -94590720), (55, 110073600), (63, 44029440), (89, -66044160), (101, -132088320), (103, 60238080), (104, 120476160), (122, -132088320), (123, -132088320), (129, 120476160), (148, 22014720)]

def pairMerged120 : Integer.Sparse (Fin 271) := [(0, 16218144), (1, -164682720), (2, 10525680), (3, 324656640), (4, 402531840), (5, 2652480), (6, -458640), (7, 12453120), (8, -576000), (12, 39398400), (13, -281779200), (15, 31726080), (18, -132088320), (21, 120476160), (23, -94245120), (24, -108172800), (25, -166164480), (26, 191197440), (27, 6480000), (30, -143596800), (32, 104302080), (33, 7603200), (34, -8628480), (37, -66044160), (38, -68636160), (41, -332812800), (42, 249143040), (43, 361428480), (44, 136857600), (45, 136857600), (46, -5806080), (47, 120476160), (49, 34214400), (50, 136615680), (51, -22014720), (53, 66044160), (54, -115741440), (55, 57196800), (63, 33454080), (66, 1321920), (89, -34318080), (101, -100362240), (103, 60238080), (104, 120476160), (105, 68428800), (106, 68428800), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (122, -132088320), (123, -132088320), (124, 31726080), (125, 31726080), (129, 120476160), (131, -10575360), (148, 11439360)]

def pairMerged121 : Integer.Sparse (Fin 271) := [(0, 28883232), (1, -293299200), (2, 51017040), (3, 829923840), (4, 685877760), (5, 2237760), (6, -458640), (7, 14112000), (8, 529920), (12, 66124800), (13, -148377600), (15, 31726080), (18, -132088320), (21, 120476160), (22, 9953280), (23, -94245120), (24, -108172800), (25, -82667520), (26, 327156480), (27, 6480000), (30, -433486080), (32, -2004480), (33, 75479040), (34, -7522560), (37, -59408640), (38, -55365120), (40, -41264640), (41, -166095360), (42, 107308800), (43, 528145920), (44, 303575040), (45, 160081920), (46, -829440), (47, 120476160), (48, 9953280), (49, -35043840), (50, 125003520), (51, -22014720), (53, 59408640), (54, -115741440), (55, 55537920), (63, 26818560), (66, 1321920), (89, -29341440), (99, 9953280), (101, -93726720), (102, 13271040), (103, 60238080), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (111, -5287680), (112, -5287680), (113, -10575360), (120, 15863040), (122, -132088320), (123, -132088320), (124, 31726080), (125, 31726080), (129, 120476160), (131, -10575360), (135, 9953280), (148, 6462720)]

def pairMerged122 : Integer.Sparse (Fin 271) := [(0, 16294680), (1, -108957780), (2, -55260), (3, 357545280), (4, 396760320), (5, 26034480), (6, -2101680), (7, -195840), (8, -12856320), (12, 65908800), (13, -175679040), (15, 146448000), (16, 50025600), (17, 87920640), (18, -296732160), (20, -220631040), (22, 9953280), (23, -83220480), (24, 123465600), (25, -315645120), (26, 344436480), (27, -99185040), (28, -176359680), (29, 220510080), (30, -234144000), (32, -83998080), (33, 75479040), (34, -19635840), (37, 79652160), (38, -55365120), (39, 176100480), (40, -41264640), (41, -166095360), (42, 251112960), (43, 528145920), (44, 303575040), (45, 160081920), (46, -438048000), (47, 202953600), (48, 9953280), (49, -230999040), (50, 383927040), (51, -47041920), (53, 82563840), (54, -91592640), (55, 155934720), (63, -7188480), (66, 7529760), (89, -89579520), (99, 9953280), (101, 8294400), (102, 13271040), (103, -22083840), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (111, -67625280), (112, -6396480), (113, -11208960), (117, 225037440), (120, 77889600), (121, 58700160), (122, -132088320), (123, -132088320), (124, -41817600), (125, 31726080), (126, 352200960), (127, -164643840), (131, -85587840), (134, -176359680), (135, 9953280), (136, -71642880), (138, -441262080), (139, -120476160), (140, -58786560), (144, 112518720), (146, 39191040), (148, 26542080), (150, -352719360)]

def pairMerged123 : Integer.Sparse (Fin 271) := [(0, 107661150), (1, 108569330), (2, -1047506780), (3, -11181755040), (4, 567605760), (5, 1015155160), (6, -46294980), (7, -2873515200), (8, -1383701280), (10, 1364895360), (12, -6638474880), (13, -6822632960), (14, 2177280), (15, 213528960), (16, -38024640), (17, 406581120), (18, -98599680), (20, -220631040), (22, 9953280), (23, 385273440), (24, 266954400), (25, -753537600), (26, -906551040), (27, -250269840), (28, -176359680), (29, 307644480), (30, -3688735680), (32, 3278920320), (33, 75479040), (34, -2041309760), (35, -561669120), (36, -1915228800), (37, -85112640), (38, -2520927360), (39, -2289461760), (40, -2771055360), (41, -166095360), (42, 647377920), (43, -109175040), (44, 303575040), (45, 3102848640), (46, 495776160), (47, -986843520), (48, 9953280), (49, -230999040), (50, 1861794720), (51, -1471774080), (53, 1631560320), (54, 2212015680), (55, -403519680), (58, 1819860480), (62, -308776320), (63, -7188480), (66, -9788640), (71, -1364895360), (72, -1364895360), (73, -1364895360), (79, 370667520), (81, -280834560), (82, 5667840), (83, -550333440), (85, -31034880), (86, 11335680), (88, -2058445440), (89, 1717476480), (92, -2941263360), (94, -1364895360), (95, -1364895360), (96, 5667840), (97, -1694502720), (98, 1471383360), (99, 681298560), (101, 8294400), (102, 13271040), (103, -22083840), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (110, -353756160), (111, -31236480), (112, 3386880), (113, -18662400), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -68697600), (131, -85587840), (133, 454965120), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -176878080), (143, 368778240), (144, 6531840), (145, 2903040), (146, 394721280), (147, -405241920), (148, -309130560), (150, -352719360)]

def pairMerged124 : Integer.Sparse (Fin 271) := [(0, 28607055), (1, 164967610), (2, 2799028965), (3, 214624800), (4, -4550304480), (5, -1873523240), (6, 163190240), (7, 1454983680), (8, 2332652160), (10, 1930970880), (12, 114093600), (13, 10633488400), (14, 2177280), (15, 213528960), (16, -38024640), (17, 406581120), (18, -98599680), (20, -220631040), (22, 9953280), (23, -6690290400), (24, -13594668480), (25, 3098561040), (26, 1112801280), (27, 6587249760), (28, -176359680), (29, -10260383040), (30, 4303512000), (31, 1811793920), (32, 9673600320), (33, 3352239360), (34, 3108460000), (35, -1630130400), (36, -3244484160), (37, 454407840), (38, -4168575360), (39, -4557669120), (40, 877625280), (41, -3144441600), (42, -658670400), (43, -3900000960), (44, 3665208960), (45, 4416958080), (46, -612787680), (47, -1541125440), (48, 9953280), (49, -4142057040), (50, -5479845120), (51, 5336209440), (53, -1660387680), (54, -2157253920), (55, 725408640), (56, 22256640), (58, -2008293120), (59, 2264051200), (60, -4070315520), (61, -8294400), (62, 8133120), (63, 158618880), (64, 2764800), (65, 309242880), (66, -9788640), (70, -2661120), (71, -864000), (72, -5045760), (73, -18869760), (74, -78243840), (75, 101606400), (76, 22809600), (77, 25453440), (79, -1131402240), (81, 53153280), (82, 93553920), (83, 323066880), (84, 80317440), (85, -31034880), (86, 11335680), (87, -4147200), (88, 177189120), (89, 274752000), (90, 46448640), (91, 291513600), (92, -274406400), (94, 100362240), (95, -216691200), (96, -217900800), (97, -13685760), (98, -29030400), (99, -2211840), (101, 8294400), (102, 13271040), (103, 61015680), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (109, -16588800), (110, 3720960), (111, -31236480), (112, 3386880), (113, -18662400), (115, 1356771840), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -68697600), (131, -85587840), (132, -465436800), (133, -969897600), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -176878080), (143, -215781120), (144, 6531840), (145, 2903040), (146, 394721280), (147, -405241920), (148, -309130560), (149, 22256640), (150, -352719360)]

def pairMerged125 : Integer.Sparse (Fin 271) := [(0, 20779368), (1, -210600080), (2, 50689520), (3, -176977920), (4, 474679680), (5, 148136960), (6, -21406640), (7, 18702720), (8, -52984320), (9, 11713280), (10, 45233280), (11, 33536640), (12, -285578880), (13, -781952000), (15, 38776320), (17, 275374080), (18, -82321920), (20, -78382080), (21, 37324800), (23, 33459840), (24, -119692800), (25, 146880000), (26, 174209280), (27, -73481760), (28, -78382080), (29, 149126400), (30, -257783040), (31, -2611200), (32, 278087040), (33, -42320640), (34, -323747200), (35, -136632960), (36, 93519360), (37, 20874240), (38, 59304960), (39, 92275200), (40, -4147200), (41, 24883200), (42, -69050880), (43, 142041600), (44, 467389440), (45, 169205760), (46, -125867520), (47, -78382080), (49, -235975680), (50, 274682880), (51, -280479360), (52, 145981440), (53, 370103040), (54, 25568640), (55, 143585280), (56, 97044480), (57, -972360), (58, 120890880), (59, -38563840), (60, -1382400), (61, -8294400), (62, 8133120), (63, 158618880), (64, 2764800), (65, -52300800), (66, -43640640), (67, 80223360), (68, 42957440), (69, 69461760), (70, -2661120), (71, -864000), (72, -5045760), (73, -18869760), (74, -78243840), (75, 101606400), (76, 22809600), (77, 25453440), (79, -46771200), (80, -77095680), (81, 53153280), (82, 93553920), (83, 323066880), (84, 80317440), (85, -31034880), (86, 11335680), (87, -4147200), (88, 177189120), (89, 274752000), (90, 46448640), (91, 291513600), (92, -274406400), (94, 100362240), (95, -216691200), (96, -217900800), (97, -13685760), (98, -29030400), (99, -2211840), (101, 8294400), (102, 13271040), (103, 61015680), (104, 79211520), (105, 158423040), (106, -829440), (107, 166717440), (108, 166717440), (109, -16588800), (110, 3720960), (111, -2488320), (112, 62709120), (113, 47001600), (114, 2488320), (115, -83297280), (116, 1451520), (117, 225037440), (120, -10160640), (122, -132088320), (124, 2903040), (125, 31726080), (126, 352200960), (127, -164643840), (130, -30032640), (131, -101727360), (132, 45941760), (133, 124369920), (134, -78382080), (135, 9953280), (136, -4561920), (138, -441262080), (139, -120476160), (140, 294969600), (142, -6497280), (143, -316391040), (144, 6531840), (145, 2903040), (146, 326039040), (147, 20632320), (148, 116743680), (149, 22256640), (150, -352719360)]

def pairMerged126 : Integer.Sparse (Fin 271) := [(0, -13225464), (1, -75312360), (2, -424080), (3, 849035520), (4, 139858560), (5, -28677600), (6, 2048400), (7, 49161600), (8, 32774400), (12, 341072640), (13, 569905920), (22, 294969600), (23, -49161600), (24, -98323200), (25, -91031040), (26, 159010560), (27, 36871200), (30, 21876480), (32, -234869760), (33, -17602560), (34, 163872000), (35, 147484800), (38, 589939200), (41, 589939200), (43, -158423040), (44, -475269120), (45, -158423040), (50, -393292800), (51, 65548800), (53, -442454400), (54, -147484800), (55, -344131200), (89, 147484800), (104, -79211520), (105, -158423040), (108, -158423040), (135, 294969600), (141, 294969600), (148, -49161600)]

def pairMerged127 : Integer.Sparse (Fin 271) := [(0, -12194280), (1, 380417400), (2, -118573200), (3, -1558080000), (4, -675561600), (5, 54050400), (6, -4096800), (7, -92505600), (8, -83520000), (12, -495043200), (13, -294969600), (15, -40435200), (17, -294969600), (22, -294969600), (23, 143510400), (24, 389318400), (25, 336182400), (26, -247392000), (27, -72748800), (30, 456710400), (32, 313200000), (34, -98323200), (38, -589939200), (41, -589939200), (43, -80870400), (47, -161740800), (50, 402796800), (51, -65548800), (53, 152236800), (54, 250560000), (55, 245808000), (63, 26956800), (66, -15660000), (89, -147484800), (91, -294969600), (92, -80870400), (110, 98323200), (111, 49161600), (112, 40435200), (113, 138758400), (117, -228355200), (125, -40435200), (126, -294969600), (131, 147484800), (135, -294969600), (137, -80870400), (140, -294969600), (141, -294969600), (147, 98323200), (148, 76118400)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged128 : Integer.Sparse (Fin 271) := [(0, -25419744), (1, 305105040), (2, -118997280), (3, -709044480), (4, -535703040), (5, 25372800), (6, -2048400), (7, -43344000), (8, -50745600), (12, -153970560), (13, 274936320), (15, -40435200), (17, -294969600), (23, 94348800), (24, 290995200), (25, 245151360), (26, -88381440), (27, -35877600), (30, 478586880), (32, 78330240), (33, -17602560), (34, 65548800), (35, 147484800), (43, -239293440), (44, -475269120), (45, -158423040), (47, -161740800), (50, 9504000), (53, -290217600), (54, 103075200), (55, -98323200), (63, 26956800), (66, -15660000), (91, -294969600), (92, -80870400), (104, -79211520), (105, -158423040), (108, -158423040), (110, 98323200), (111, 49161600), (112, 40435200), (113, 138758400), (117, -228355200), (125, -40435200), (126, -294969600), (131, 147484800), (137, -80870400), (140, -294969600), (147, 98323200), (148, 26956800)]

def pairMerged129 : Integer.Sparse (Fin 271) := [(0, 8872128), (1, -256813920), (2, 70392960), (3, 1050232320), (4, 503700480), (5, -17216640), (6, 853920), (7, 55203840), (8, 14400000), (12, 394767360), (13, 93242880), (15, 1658880), (18, 117987840), (23, -157870080), (24, -80870400), (25, -551715840), (26, 124070400), (27, 39744000), (30, -434833920), (32, -201070080), (33, 1290240), (34, 40250880), (36, 3317760), (42, 117987840), (43, 117987840), (46, 117987840), (47, 235975680), (49, 235975680), (50, -357281280), (51, 39697920), (53, -157317120), (54, -80317440), (55, -78658560), (63, -79764480), (66, 138240), (92, 117987840), (96, 117987840), (99, 3317760), (102, 3317760), (112, -552960), (113, -1658880), (117, 3317760), (118, 1658880), (122, 117987840), (125, 1658880), (126, 1658880), (127, 235975680), (131, -552960), (139, 117987840), (146, -552960), (148, -40435200)]

def pairMerged130 : Integer.Sparse (Fin 271) := [(0, -8782848), (1, 153694080), (2, -48994560), (3, -807045120), (4, -393431040), (5, 6128640), (6, -766080), (7, -8294400), (8, -4147200), (12, -64696320), (13, -52807680), (18, -35665920), (21, -37324800), (26, -405688320), (30, 73543680), (32, 122204160), (33, -72990720), (34, -24514560), (36, -74649600), (39, -37324800), (50, 12441600), (51, -12072960), (52, -145981440), (54, 61102080), (55, 24883200), (56, -108656640), (107, -145981440), (119, -35665920), (127, -71331840), (128, -37324800), (135, -37324800)]

def pairMerged131 : Integer.Sparse (Fin 271) := [(0, 89280), (1, -103119840), (2, 21398400), (3, 243187200), (4, 110269440), (5, -11088000), (6, 87840), (7, 46909440), (8, 10252800), (12, 330071040), (13, 40435200), (15, 1658880), (18, 82321920), (21, -37324800), (23, -157870080), (24, -80870400), (25, -551715840), (26, -281617920), (27, 39744000), (30, -361290240), (32, -78865920), (33, -71700480), (34, 15736320), (36, -71331840), (39, -37324800), (42, 117987840), (43, 117987840), (46, 117987840), (47, 235975680), (49, 235975680), (50, -344839680), (51, 27624960), (52, -145981440), (53, -157317120), (54, -19215360), (55, -53775360), (56, -108656640), (63, -79764480), (66, 138240), (92, 117987840), (96, 117987840), (99, 3317760), (102, 3317760), (107, -145981440), (112, -552960), (113, -1658880), (117, 3317760), (118, 1658880), (119, -35665920), (122, 117987840), (125, 1658880), (126, 1658880), (127, 164643840), (128, -37324800), (131, -552960), (135, -37324800), (139, 117987840), (146, -552960), (148, -40435200)]

def pairMerged132 : Integer.Sparse (Fin 271) := [(0, -25330464), (1, 201985200), (2, -97598880), (3, -465857280), (4, -425433600), (5, 14284800), (6, -1960560), (7, 3565440), (8, -40492800), (12, 176100480), (13, 315371520), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -369999360), (27, 3866400), (30, 117296640), (32, -535680), (33, -89303040), (34, 81285120), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -335335680), (51, 27624960), (52, -145981440), (53, -447534720), (54, 83859840), (55, -152098560), (56, -108656640), (63, -52807680), (66, -15521760), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, 98323200), (111, 49161600), (112, 39882240), (113, 137099520), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (131, 146931840), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (146, -552960), (147, 98323200), (148, -13478400)]

def pairMerged133 : Integer.Sparse (Fin 271) := [(0, 480456), (1, -15346440), (2, -30987000), (3, -25176960), (5, 90128160), (6, -12461040), (7, -88629120), (8, -92655360), (9, 56429280), (34, -36253440), (51, -16104960), (57, -1803960), (67, -113806080), (68, -59086080), (69, -185310720), (163, 31726080), (164, -14601600), (183, -12078720), (222, -16104960), (247, 12078720), (268, 24157440)]

def pairMerged134 : Integer.Sparse (Fin 271) := [(0, -134328), (1, 9644880), (2, -5616120), (3, -208915200), (4, -68348160), (5, 62546400), (6, -11042280), (7, -11612160), (9, 15690720), (11, -68348160), (26, -136696320), (34, -211495680), (51, -183552000), (54, 96716160), (57, -752280), (67, -7741440), (68, -5160960), (143, 205044480), (164, -14616960), (183, -3870720), (222, -7741440), (247, 11612160), (248, 96716160), (249, 64477440)]

def pairMerged135 : Integer.Sparse (Fin 271) := [(0, 346128), (1, -5701560), (2, -36603120), (3, -234092160), (4, -68348160), (5, 152674560), (6, -23503320), (7, -100241280), (8, -92655360), (9, 72120000), (11, -68348160), (26, -136696320), (34, -247749120), (51, -199656960), (54, 96716160), (57, -2556240), (67, -121547520), (68, -64247040), (69, -185310720), (143, 205044480), (163, 31726080), (164, -29218560), (183, -15949440), (222, -23846400), (247, 23690880), (248, 96716160), (249, 64477440), (268, 24157440)]

def pairMerged136 : Integer.Sparse (Fin 271) := [(0, -229104), (1, 4459320), (2, 11559840), (3, 56712960), (4, 576000), (5, -21784320), (6, 3760560), (7, 22936320), (8, 5760000), (9, -5734080), (12, 17752320), (13, 79885440), (34, 63285120), (50, -5184000), (51, 54984960), (53, -26628480), (57, 220920), (67, 12332160), (68, 7069440), (69, 6912000), (80, 47339520), (115, 44380800), (132, -53256960), (133, -53256960), (164, 11834880), (181, -5184000), (182, -3456000), (183, 9452160), (219, -26628480), (222, 17752320), (246, -17752320), (247, -26628480)]

def pairMerged137 : Integer.Sparse (Fin 271) := [(0, -554040), (1, 11746800), (2, -4980600), (3, -45336960), (4, -12792960), (5, 5163840), (6, 2489400), (7, -55883520), (8, -13916160), (9, -10238400), (11, 5834880), (13, 23339520), (26, -6958080), (27, -6985440), (34, -2246400), (50, 55883520), (51, 8300160), (55, -35009280), (57, 147240), (66, -6985440), (67, -31420800), (69, 4711680), (80, 23339520), (111, 27941760), (113, 55883520), (115, 29174400), (133, -70018560), (143, -17504640), (164, 5834880), (181, 55883520), (183, -6958080), (219, -17504640), (220, 55883520), (222, -6958080), (263, -70018560), (268, -35009280)]

def pairMerged138 : Integer.Sparse (Fin 271) := [(0, -783144), (1, 16206120), (2, 6579240), (3, 11376000), (4, -12216960), (5, -16620480), (6, 6249960), (7, -32947200), (8, -8156160), (9, -15972480), (11, 5834880), (12, 17752320), (13, 103224960), (26, -6958080), (27, -6985440), (34, 61038720), (50, 50699520), (51, 63285120), (53, -26628480), (55, -35009280), (57, 368160), (66, -6985440), (67, -19088640), (68, 7069440), (69, 11623680), (80, 70679040), (111, 27941760), (113, 55883520), (115, 73555200), (132, -53256960), (133, -123275520), (143, -17504640), (164, 17669760), (181, 50699520), (182, -3456000), (183, 2494080), (219, -44133120), (220, 55883520), (222, 10794240), (246, -17752320), (247, -26628480), (263, -70018560), (268, -35009280)]

def pairMerged139 : Integer.Sparse (Fin 271) := [(0, -437016), (1, 10504560), (2, -30023880), (3, -222716160), (4, -80565120), (5, 136054080), (6, -17253360), (7, -133188480), (8, -100811520), (9, 56147520), (11, -62513280), (12, 17752320), (13, 103224960), (26, -143654400), (27, -6985440), (34, -186710400), (50, 50699520), (51, -136371840), (53, -26628480), (54, 96716160), (55, -35009280), (57, -2188080), (66, -6985440), (67, -140636160), (68, -57177600), (69, -173687040), (80, 70679040), (111, 27941760), (113, 55883520), (115, 73555200), (132, -53256960), (133, -123275520), (143, 187539840), (163, 31726080), (164, -11548800), (181, 50699520), (182, -3456000), (183, -13455360), (219, -44133120), (220, 55883520), (222, -13052160), (246, -17752320), (247, -2937600), (248, 96716160), (249, 64477440), (263, -70018560), (268, -10851840)]

def pairMerged140 : Integer.Sparse (Fin 271) := [(0, -25767480), (1, 212489760), (2, -127622760), (3, -688573440), (4, -505998720), (5, 150338880), (6, -19213920), (7, -129623040), (8, -141304320), (9, 56147520), (11, -62513280), (12, 193852800), (13, 418596480), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -513653760), (27, -3119040), (30, 117296640), (32, -535680), (33, -89303040), (34, -105425280), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -284636160), (51, -108746880), (52, -145981440), (53, -474163200), (54, 180576000), (55, -187107840), (56, -108656640), (57, -2188080), (63, -52807680), (66, -22507200), (67, -140636160), (68, -57177600), (69, -173687040), (80, 70679040), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, 98323200), (111, 77103360), (112, 39882240), (113, 192983040), (115, 73555200), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (131, 146931840), (132, -53256960), (133, -123275520), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 187539840), (146, -552960), (147, 98323200), (148, -13478400), (163, 31726080), (164, -11548800), (181, 50699520), (182, -3456000), (183, -13455360), (219, -44133120), (220, 55883520), (222, -13052160), (246, -17752320), (247, -2937600), (248, 96716160), (249, 64477440), (263, -70018560), (268, -10851840)]

def pairMerged141 : Integer.Sparse (Fin 271) := [(0, 294408), (1, -8806320), (2, -8317080), (3, 49213440), (4, 30620160), (5, -14554080), (6, -951480), (7, -22291200), (8, -8916480), (9, -1283040), (11, 30620160), (12, -17832960), (13, -75790080), (26, 76550400), (27, 11482560), (34, 67046400), (50, 26749440), (51, -22878720), (53, 13374720), (54, -22965120), (57, 199800), (66, 8138880), (67, -8916480), (68, -8916480), (69, -4458240), (80, -17832960), (112, 26749440), (113, 13374720), (115, -22291200), (148, -91860480), (164, 3196800), (182, 26749440), (183, -8916480), (219, 13374720), (220, -45930240), (221, 26749440), (222, 6393600), (248, -22965120)]

def pairMerged142 : Integer.Sparse (Fin 271) := [(0, -668736), (1, 8665920), (2, 44087040), (3, 97920000), (4, 3317760), (5, -152421120), (6, 13080960), (7, 17372160), (8, 104232960), (9, -34744320), (12, 3317760), (13, 4423680), (26, 3317760), (27, 39709440), (34, 3317760), (50, -9953280), (51, 107550720), (54, -9953280), (57, 2171520), (66, 39087360), (67, 17372160), (69, 86860800), (113, -52116480), (114, -2488320), (115, 829440), (146, -104232960), (147, -104232960), (181, -52116480), (183, 17372160), (220, -9953280), (221, -6635520), (222, 1105920)]

def pairMerged143 : Integer.Sparse (Fin 271) := [(0, -374328), (1, -140400), (2, 35769960), (3, 147133440), (4, 33937920), (5, -166975200), (6, 12129480), (7, -4919040), (8, 95316480), (9, -36027360), (11, 30620160), (12, -14515200), (13, -71366400), (26, 79868160), (27, 51192000), (34, 70364160), (50, 16796160), (51, 84672000), (53, 13374720), (54, -32918400), (57, 2371320), (66, 47226240), (67, 8455680), (68, -8916480), (69, 82402560), (80, -17832960), (112, 26749440), (113, -38741760), (114, -2488320), (115, -21461760), (146, -104232960), (147, -104232960), (148, -91860480), (164, 3196800), (181, -52116480), (182, 26749440), (183, 8455680), (219, 13374720), (220, -55883520), (221, 20113920), (222, 7499520), (248, -22965120)]

def pairMerged144 : Integer.Sparse (Fin 271) := [(0, -710208), (1, 1988640), (2, 2613600), (3, 53464320), (4, 4999680), (5, -47597760), (6, 2922480), (7, 9999360), (8, 9999360), (9, -11263680), (11, 16704000), (12, 3352320), (13, 50169600), (26, 43407360), (34, 96871680), (51, 33465600), (54, -10056960), (55, -14999040), (57, 834480), (66, 16277760), (68, 9999360), (69, 14999040), (80, 16704000), (115, 6704640), (131, -29998080), (146, -14999040), (147, -20113920), (148, -14999040), (164, 8352000), (182, -14999040), (183, 4999680), (221, -20113920), (222, 6704640), (249, -10056960), (263, -14999040)]

def pairMerged145 : Integer.Sparse (Fin 271) := [(0, 527616), (1, -14679360), (2, -21980160), (3, -35182080), (5, 71337600), (6, -7646400), (7, -79833600), (8, -80732160), (9, 17815680), (13, -6428160), (26, -6428160), (34, -63636480), (51, -53222400), (53, 19284480), (59, -4285440), (67, -140382720), (68, -64235520), (69, -194503680), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (222, -22325760)]

def pairMerged146 : Integer.Sparse (Fin 271) := [(0, -182592), (1, -12690720), (2, -19366560), (3, 18282240), (4, 4999680), (5, 23739840), (6, -4723920), (7, -69834240), (8, -70732800), (9, 6552000), (11, 16704000), (12, 3352320), (13, 43741440), (26, 36979200), (34, 33235200), (51, -19756800), (53, 19284480), (54, -10056960), (55, -14999040), (57, 834480), (59, -4285440), (66, 16277760), (67, -140382720), (68, -54236160), (69, -179504640), (80, 16704000), (115, 6704640), (131, -29998080), (146, -14999040), (147, -20113920), (148, -14999040), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (164, 8352000), (182, -14999040), (183, 4999680), (221, -20113920), (222, -15621120), (249, -10056960), (263, -14999040)]

def pairMerged147 : Integer.Sparse (Fin 271) := [(0, -556920), (1, -12831120), (2, 16403400), (3, 165415680), (4, 38937600), (5, -143235360), (6, 7405560), (7, -74753280), (8, 24583680), (9, -29475360), (11, 47324160), (12, -11162880), (13, -27624960), (26, 116847360), (27, 51192000), (34, 103599360), (50, 16796160), (51, 64915200), (53, 32659200), (54, -42975360), (55, -14999040), (57, 3205800), (59, -4285440), (66, 63504000), (67, -131927040), (68, -63152640), (69, -97102080), (80, -1128960), (112, 26749440), (113, -38741760), (114, -2488320), (115, -14757120), (131, -29998080), (146, -119232000), (147, -124346880), (148, -106859520), (151, 60549120), (152, -17740800), (153, 19284480), (154, 12856320), (164, 11548800), (181, -52116480), (182, 11750400), (183, 13455360), (219, 13374720), (220, -55883520), (222, -8121600), (248, -22965120), (249, -10056960), (263, -14999040)]

def pairMerged148 : Integer.Sparse (Fin 271) := [(0, -758592), (1, 8985600), (2, 20851200), (3, 129162240), (4, 18570240), (5, -66366720), (6, 6580800), (7, 145244160), (8, 80916480), (9, -9699840), (13, 3317760), (26, 54051840), (34, 163814400), (50, -2488320), (51, 62346240), (55, -4976640), (58, -4976640), (65, 35481600), (67, 94510080), (68, 54051840), (69, 83404800), (79, -53222400), (115, 1658880), (151, -55710720), (152, 17740800), (153, -2488320), (155, -9953280), (222, 19399680)]

def pairMerged149 : Integer.Sparse (Fin 271) := [(0, 28944), (1, -25316280), (2, 3903840), (3, 336885120), (4, 73889280), (5, -19432800), (6, 4088520), (7, 82460160), (9, -1896480), (12, 4285440), (13, 103789440), (26, 235952640), (33, 107089920), (34, 178220160), (51, 36944640), (54, -68273280), (59, 2856960), (63, -110833920), (65, 82460160), (67, 6157440), (68, 22757760), (69, 1428480), (112, -55416960), (131, -12856320), (152, 15171840), (156, -36944640), (158, -8570880)]

def pairMerged150 : Integer.Sparse (Fin 271) := [(0, -729648), (1, -16330680), (2, 24755040), (3, 466047360), (4, 92459520), (5, -85799520), (6, 10669320), (7, 227704320), (8, 80916480), (9, -11596320), (12, 4285440), (13, 107107200), (26, 290004480), (33, 107089920), (34, 342034560), (50, -2488320), (51, 99290880), (54, -68273280), (55, -4976640), (58, -4976640), (59, 2856960), (63, -110833920), (65, 117941760), (67, 100667520), (68, 76809600), (69, 84833280), (79, -53222400), (112, -55416960), (115, 1658880), (131, -12856320), (151, -55710720), (152, 32912640), (153, -2488320), (155, -9953280), (156, -36944640), (158, -8570880), (222, 19399680)]

def pairMerged151 : Integer.Sparse (Fin 271) := [(0, 338040), (1, 378720), (2, 461880), (3, -61228800), (4, -2856960), (5, 22893120), (6, -4328640), (7, -42658560), (8, -2856960), (9, 7228800), (13, -29456640), (26, -48372480), (33, -19457280), (34, -95316480), (51, -18570240), (53, 36944640), (55, 8570880), (59, -7142400), (63, 4285440), (65, -27486720), (67, -16600320), (68, -27486720), (69, -15171840), (111, 18472320), (112, 8570880), (113, 4285440), (115, -5713920), (130, 18472320), (131, 41230080), (152, -15171840), (153, 36944640), (154, 4285440), (155, 8570880), (156, 36944640), (158, 8570880), (222, -16600320)]

def pairMerged152 : Integer.Sparse (Fin 271) := [(0, -1415088), (1, 13188240), (2, -8188560), (3, -70548480), (4, -46828800), (5, -50230080), (6, 15040080), (7, -9492480), (8, 45043200), (9, -22968000), (10, 19560960), (11, -13040640), (12, -6520320), (13, -13040640), (26, -51575040), (32, 39121920), (33, -26081280), (34, -86549760), (50, -55123200), (51, 26668800), (54, 19560960), (65, -65203200), (67, 73497600), (68, 18374400), (69, 110246400), (79, 156487680), (80, -6520320), (110, -110246400), (111, -110246400), (113, -55123200), (131, -55123200), (143, 39121920), (146, -110246400), (153, -55123200), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 18374400)]

def pairMerged153 : Integer.Sparse (Fin 271) := [(0, -1077048), (1, 13566960), (2, -7726680), (3, -131777280), (4, -49685760), (5, -27336960), (6, 10711440), (7, -52151040), (8, 42186240), (9, -15739200), (10, 19560960), (11, -13040640), (12, -6520320), (13, -42497280), (26, -99947520), (32, 39121920), (33, -45538560), (34, -181866240), (50, -55123200), (51, 8098560), (53, 36944640), (54, 19560960), (55, 8570880), (59, -7142400), (63, 4285440), (65, -92689920), (67, 56897280), (68, -9112320), (69, 95074560), (79, 156487680), (80, -6520320), (110, -110246400), (111, -91774080), (112, 8570880), (113, -50837760), (115, -5713920), (130, 18472320), (131, -13893120), (143, 39121920), (146, -110246400), (152, -15171840), (153, -18178560), (154, 4285440), (155, 8570880), (156, 36944640), (158, 8570880), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 1774080)]

def pairMerged154 : Integer.Sparse (Fin 271) := [(0, -1806696), (1, -2763720), (2, 17028360), (3, 334270080), (4, 42773760), (5, -113136480), (6, 21380760), (7, 175553280), (8, 123102720), (9, -27335520), (10, 19560960), (11, -13040640), (12, -2234880), (13, 64609920), (26, 190056960), (32, 39121920), (33, 61551360), (34, 160168320), (50, -57611520), (51, 107389440), (53, 36944640), (54, -48712320), (55, 3594240), (58, -4976640), (59, -4285440), (63, -106548480), (65, 25251840), (67, 157564800), (68, 67697280), (69, 179907840), (79, 103265280), (80, -6520320), (110, -110246400), (111, -91774080), (112, -46846080), (113, -50837760), (115, -4055040), (130, 18472320), (131, -26749440), (143, 39121920), (146, -110246400), (151, -55710720), (152, 17740800), (153, -20666880), (154, 4285440), (155, -1382400), (160, 39121920), (162, -13040640), (179, 39121920), (180, 39121920), (222, 21173760)]

def pairMerged155 : Integer.Sparse (Fin 271) := [(0, -2363616), (1, -15594840), (2, 33431760), (3, 499685760), (4, 81711360), (5, -256371840), (6, 28786320), (7, 100800000), (8, 147686400), (9, -56810880), (10, 19560960), (11, 34283520), (12, -13397760), (13, 36984960), (26, 306904320), (27, 51192000), (32, 39121920), (33, 61551360), (34, 263767680), (50, -40815360), (51, 172304640), (53, 69603840), (54, -91687680), (55, -11404800), (57, 3205800), (58, -4976640), (59, -8570880), (63, -106548480), (65, 25251840), (66, 63504000), (67, 25637760), (68, 4544640), (69, 82805760), (79, 103265280), (80, -7649280), (110, -110246400), (111, -91774080), (112, -20096640), (113, -89579520), (114, -2488320), (115, -18812160), (130, 18472320), (131, -56747520), (143, 39121920), (146, -229478400), (147, -124346880), (148, -106859520), (151, 4838400), (153, -1382400), (154, 17141760), (155, -1382400), (160, 39121920), (162, -13040640), (164, 11548800), (179, 39121920), (180, 39121920), (181, -52116480), (182, 11750400), (183, 13455360), (219, 13374720), (220, -55883520), (222, 13052160), (248, -22965120), (249, -10056960), (263, -14999040)]

def pairMerged156 : Integer.Sparse (Fin 271) := [(0, -28131096), (1, 196894920), (2, -94191000), (3, -188887680), (4, -424287360), (5, -106032960), (6, 9572400), (7, -28823040), (8, 6382080), (9, -663360), (10, 19560960), (11, -28229760), (12, 180455040), (13, 455581440), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -63521280), (24, 210124800), (25, -306564480), (26, -206749440), (27, 48072960), (30, 117296640), (32, 38586240), (33, -27751680), (34, 158342400), (35, 147484800), (36, -71331840), (39, -37324800), (42, 117987840), (43, -121305600), (44, -475269120), (45, -158423040), (46, 117987840), (47, 74234880), (49, 235975680), (50, -325451520), (51, 63557760), (52, -145981440), (53, -404559360), (54, 88888320), (55, -198512640), (56, -108656640), (57, 1017720), (58, -4976640), (59, -8570880), (63, -159356160), (65, 25251840), (66, 40996800), (67, -114998400), (68, -52632960), (69, -90881280), (79, 103265280), (80, 63029760), (91, -294969600), (92, 37117440), (96, 117987840), (99, 3317760), (102, 3317760), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (110, -11923200), (111, -14670720), (112, 19785600), (113, 103403520), (114, -2488320), (115, 54743040), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (130, 18472320), (131, 90184320), (132, -53256960), (133, -123275520), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 226661760), (146, -230031360), (147, -26023680), (148, -120337920), (151, 4838400), (153, -1382400), (154, 17141760), (155, -1382400), (160, 39121920), (162, -13040640), (163, 31726080), (179, 39121920), (180, 39121920), (181, -1416960), (182, 8294400), (219, -30758400), (246, -17752320), (247, -2937600), (248, 73751040), (249, 54420480), (263, -85017600), (268, -10851840)]

def pairMerged157 : Integer.Sparse (Fin 271) := [(0, -543168), (1, 1853440), (2, 15278400), (3, 173967360), (4, 29936640), (5, -32602880), (6, 3902720), (7, 62622720), (8, 21765120), (11, 13593600), (12, 29821440), (13, 111191040), (26, 76216320), (32, -32532480), (33, 27187200), (34, 144133120), (51, 84157440), (53, -16266240), (58, -81331200), (59, 27136000), (65, 32686080), (79, -49029120), (80, 10844160), (115, 32532480), (132, -8133120), (133, -16266240), (143, -40780800), (159, -16266240), (160, -24514560), (162, 13593600), (218, -32532480), (245, -32532480)]

def pairMerged158 : Integer.Sparse (Fin 271) := [(0, 24960), (1, 270720), (2, -679680), (3, -10321920), (4, -2304000), (5, 1244160), (6, -161280), (7, -2211840), (8, -737280), (11, -1474560), (12, -2211840), (13, -5130240), (26, -4515840), (31, -153600), (32, 3870720), (33, -1658880), (34, -6266880), (50, 1382400), (51, -3409920), (53, 552960), (55, 1105920), (58, 1105920), (59, -1198080), (60, 1382400), (65, -737280), (79, 2211840), (114, 1382400), (115, -645120), (143, 5529600), (159, 552960), (161, 1105920), (162, -552960), (217, 2764800), (218, 2211840), (245, 1105920)]

def pairMerged159 : Integer.Sparse (Fin 271) := [(0, -518208), (1, 2124160), (2, 14598720), (3, 163645440), (4, 27632640), (5, -31358720), (6, 3741440), (7, 60410880), (8, 21027840), (11, 12119040), (12, 27609600), (13, 106060800), (26, 71700480), (31, -153600), (32, -28661760), (33, 25528320), (34, 137866240), (50, 1382400), (51, 80747520), (53, -15713280), (55, 1105920), (58, -80225280), (59, 25937920), (60, 1382400), (65, 31948800), (79, -46817280), (80, 10844160), (114, 1382400), (115, 31887360), (132, -8133120), (133, -16266240), (143, -35251200), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (217, 2764800), (218, -30320640), (245, -31426560)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged160 : Integer.Sparse (Fin 271) := [(0, -322560), (1, 720000), (2, 1324800), (3, 23500800), (5, -8870400), (6, 1411200), (11, 1382400), (12, 2304000), (13, 23961600), (26, 8294400), (32, -5529600), (33, 921600), (34, 18432000), (51, 21657600), (54, -4147200), (59, 921600), (62, -8294400), (80, 1843200), (110, -11059200), (115, 3225600), (147, -11059200), (179, -5529600), (217, -2764800), (245, -4147200)]

def pairMerged161 : Integer.Sparse (Fin 271) := [(0, 603720), (1, 6866280), (2, -3958560), (3, -88750080), (5, 6340320), (6, -429840), (7, -36616320), (8, -8847360), (9, -72000), (10, 6825600), (12, -15926400), (13, -4550400), (23, 54604800), (24, 27302400), (26, -9100800), (27, -11944800), (34, -20494080), (50, 40953600), (51, 1935360), (53, 47779200), (54, 40953600), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (143, 27302400), (151, -5806080), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (247, -1451520), (268, -2903040)]

def pairMerged162 : Integer.Sparse (Fin 271) := [(0, 281160), (1, 7586280), (2, -2633760), (3, -65249280), (5, -2530080), (6, 981360), (7, -36616320), (8, -8847360), (9, -72000), (10, 6825600), (11, 1382400), (12, -13622400), (13, 19411200), (23, 54604800), (24, 27302400), (26, -806400), (27, -11944800), (32, -5529600), (33, 921600), (34, -2062080), (50, 40953600), (51, 23592960), (53, 47779200), (54, 36806400), (59, 921600), (62, -8294400), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (80, 1843200), (110, -11059200), (115, 3225600), (143, 27302400), (147, -11059200), (151, -5806080), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (179, -5529600), (217, -2764800), (245, -4147200), (247, -1451520), (268, -2903040)]

def pairMerged163 : Integer.Sparse (Fin 271) := [(0, -237048), (1, 9710440), (2, 11964960), (3, 98396160), (4, 27632640), (5, -33888800), (6, 4722800), (7, 23794560), (8, 12180480), (9, -72000), (10, 6825600), (11, 13501440), (12, 13987200), (13, 125472000), (23, 54604800), (24, 27302400), (26, 70894080), (27, -11944800), (31, -153600), (32, -34191360), (33, 26449920), (34, 135804160), (50, 42336000), (51, 104340480), (53, 32065920), (54, 36806400), (55, 1105920), (58, -80225280), (59, 26859520), (60, 1382400), (62, -8294400), (65, 31948800), (67, -2828160), (68, -4083840), (69, 12222720), (75, -81907200), (77, -20476800), (79, -46817280), (80, 12687360), (110, -11059200), (114, 1382400), (115, 35112960), (132, -8133120), (133, -16266240), (143, -7948800), (147, -11059200), (151, -5806080), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, 5374080), (165, 1451520), (166, 5806080), (167, 5806080), (174, -40953600), (175, -61430400), (179, -5529600), (218, -30320640), (245, -35573760), (247, -1451520), (268, -2903040)]

def pairMerged164 : Integer.Sparse (Fin 271) := [(0, 467424), (1, -1856160), (2, -15180480), (3, -52646400), (4, -3801600), (5, 25424640), (6, -1509120), (7, -57945600), (8, -43361280), (9, 3018240), (10, 16312320), (12, -11243520), (13, -12879360), (23, 2903040), (24, 13409280), (26, -2534400), (27, -4078080), (29, 3801600), (34, -33431040), (50, 34629120), (51, -11543040), (53, 15413760), (54, 3801600), (55, 15206400), (58, 30827520), (67, -20113920), (68, -6105600), (69, -41886720), (70, -8709120), (71, -17418240), (72, -40227840), (73, -11404800), (76, -22809600), (132, 8709120), (133, 7603200), (143, 7603200), (151, 19215360), (163, 6704640), (165, -8709120), (166, -28823040), (168, -11404800), (172, -22809600), (173, -22809600), (247, 12510720), (268, 3801600)]

def pairMerged165 : Integer.Sparse (Fin 271) := [(0, 432288), (1, -8563680), (2, -17930880), (3, -29698560), (4, -1359360), (5, 30919680), (6, -2249280), (7, -30965760), (8, -49489920), (9, 2131200), (10, 276480), (12, -92160), (13, -46080), (23, 414720), (24, 138240), (26, -92160), (27, -69120), (34, -13109760), (50, 12510720), (51, -24560640), (53, 691200), (54, 138240), (58, 276480), (67, -18593280), (68, -7349760), (69, -27555840), (70, -829440), (71, -414720), (75, -829440), (79, 16312320), (84, -24468480), (132, 276480), (143, 276480), (151, 8432640), (163, 138240), (165, -414720), (167, -24468480), (168, -414720), (170, -829440), (171, -829440), (194, -12234240), (197, -24468480), (199, -24468480), (247, 276480), (268, 12234240)]

def pairMerged166 : Integer.Sparse (Fin 271) := [(0, 899712), (1, -10419840), (2, -33111360), (3, -82344960), (4, -5160960), (5, 56344320), (6, -3758400), (7, -88911360), (8, -92851200), (9, 5149440), (10, 16588800), (12, -11335680), (13, -12925440), (23, 3317760), (24, 13547520), (26, -2626560), (27, -4147200), (29, 3801600), (34, -46540800), (50, 47139840), (51, -36103680), (53, 16104960), (54, 3939840), (55, 15206400), (58, 31104000), (67, -38707200), (68, -13455360), (69, -69442560), (70, -9538560), (71, -17832960), (72, -40227840), (73, -11404800), (75, -829440), (76, -22809600), (79, 16312320), (84, -24468480), (132, 8985600), (133, 7603200), (143, 7879680), (151, 27648000), (163, 6842880), (165, -9123840), (166, -28823040), (167, -24468480), (168, -11819520), (170, -829440), (171, -829440), (172, -22809600), (173, -22809600), (194, -12234240), (197, -24468480), (199, -24468480), (247, 12787200), (268, 16035840)]

def pairMerged167 : Integer.Sparse (Fin 271) := [(0, -480096), (1, 5484960), (2, 17333280), (3, 56056320), (4, 9446400), (5, -31104000), (6, 2106720), (7, 50457600), (8, 44997120), (9, -2407680), (12, 1704960), (13, 7557120), (24, -2557440), (26, 7188480), (34, 35089920), (50, -26887680), (51, 28753920), (55, -18662400), (58, -15552000), (67, 20298240), (68, 8593920), (69, 27555840), (71, 15344640), (74, 37324800), (75, 9331200), (79, -10229760), (82, 7672320), (83, 15344640), (133, -17556480), (143, -10782720), (151, -21565440), (163, -7672320), (165, 7672320), (166, 15344640), (167, 18662400), (170, 18662400), (171, 9331200), (172, 18662400), (194, 23016960), (199, 15344640), (247, -5667840), (268, -13893120)]

def pairMerged168 : Integer.Sparse (Fin 271) := [(0, 589032), (1, 3965760), (2, 2307240), (3, -60883200), (4, 852480), (5, -6760800), (6, 449280), (7, -22037760), (8, 32394240), (9, 2191680), (12, -15586560), (13, -15586560), (23, 23379840), (26, 1704960), (30, 46759680), (32, 46759680), (34, -21795840), (50, -7672320), (51, -17533440), (67, -7914240), (68, -14734080), (69, 25574400), (79, 93519360), (83, 15344640), (88, -140279040), (111, 23379840), (130, 23379840), (143, -5114880), (151, 41644800), (163, -2557440), (166, 7672320), (194, -132606720), (197, 15344640), (199, 15344640), (205, -140279040), (268, 41644800)]

def pairMerged169 : Integer.Sparse (Fin 271) := [(0, 108936), (1, 9450720), (2, 19640520), (3, -4826880), (4, 10298880), (5, -37864800), (6, 2556000), (7, 28419840), (8, 77391360), (9, -216000), (12, -13881600), (13, -8029440), (23, 23379840), (24, -2557440), (26, 8893440), (30, 46759680), (32, 46759680), (34, 13294080), (50, -34560000), (51, 11220480), (55, -18662400), (58, -15552000), (67, 12384000), (68, -6140160), (69, 53130240), (71, 15344640), (74, 37324800), (75, 9331200), (79, 83289600), (82, 7672320), (83, 30689280), (88, -140279040), (111, 23379840), (130, 23379840), (133, -17556480), (143, -15897600), (151, 20079360), (163, -10229760), (165, 7672320), (166, 23016960), (167, 18662400), (170, 18662400), (171, 9331200), (172, 18662400), (194, -109589760), (197, 15344640), (199, 30689280), (205, -140279040), (247, -5667840), (268, 27751680)]

def pairMerged170 : Integer.Sparse (Fin 271) := [(0, 1008648), (1, -969120), (2, -13470840), (3, -87171840), (4, 5137920), (5, 18479520), (6, -1202400), (7, -60491520), (8, -15459840), (9, 4933440), (10, 16588800), (12, -25217280), (13, -20954880), (23, 26697600), (24, 10990080), (26, 6266880), (27, -4147200), (29, 3801600), (30, 46759680), (32, 46759680), (34, -33246720), (50, 12579840), (51, -24883200), (53, 16104960), (54, 3939840), (55, -3456000), (58, 15552000), (67, -26323200), (68, -19595520), (69, -16312320), (70, -9538560), (71, -2488320), (72, -40227840), (73, -11404800), (74, 37324800), (75, 8501760), (76, -22809600), (79, 99601920), (82, 7672320), (83, 30689280), (84, -24468480), (88, -140279040), (111, 23379840), (130, 23379840), (132, 8985600), (133, -9953280), (143, -8017920), (151, 47727360), (163, -3386880), (165, -1451520), (166, -5806080), (167, -5806080), (168, -11819520), (170, 17832960), (171, 8501760), (172, -4147200), (173, -22809600), (194, -121824000), (197, -9123840), (199, 6220800), (205, -140279040), (247, 7119360), (268, 43787520)]

def pairMerged171 : Integer.Sparse (Fin 271) := [(0, 771600), (1, 8741320), (2, -1505880), (3, 11224320), (4, 32770560), (5, -15409280), (6, 3520400), (7, -36696960), (8, -3279360), (9, 4861440), (10, 23414400), (11, 13501440), (12, -11230080), (13, 104517120), (23, 81302400), (24, 38292480), (26, 77160960), (27, -16092000), (29, 3801600), (30, 46759680), (31, -153600), (32, 12568320), (33, 26449920), (34, 102557440), (50, 54915840), (51, 79457280), (53, 48170880), (54, 40746240), (55, -2350080), (58, -64673280), (59, 26859520), (60, 1382400), (62, -8294400), (65, 31948800), (67, -29151360), (68, -23679360), (69, -4089600), (70, -9538560), (71, -2488320), (72, -40227840), (73, -11404800), (74, 37324800), (75, -73405440), (76, -22809600), (77, -20476800), (79, 52784640), (80, 12687360), (82, 7672320), (83, 30689280), (84, -24468480), (88, -140279040), (110, -11059200), (111, 23379840), (114, 1382400), (115, 35112960), (130, 23379840), (132, 852480), (133, -26219520), (143, -15966720), (147, -11059200), (151, 41921280), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, 1987200), (168, -11819520), (170, 17832960), (171, 8501760), (172, -4147200), (173, -22809600), (174, -40953600), (175, -61430400), (179, -5529600), (194, -121824000), (197, -9123840), (199, 6220800), (205, -140279040), (218, -30320640), (245, -35573760), (247, 5667840), (268, 40884480)]

def pairMerged172 : Integer.Sparse (Fin 271) := [(0, -1147608), (1, -38194200), (2, 82209600), (3, 411903360), (4, 58924800), (5, -36447840), (6, 1829520), (7, -29272320), (8, 71470080), (9, -760320), (12, 99601920), (13, 65387520), (23, -32503680), (24, -9123840), (25, 94089600), (26, 36875520), (32, -374077440), (34, -11594880), (51, 84015360), (53, -22809600), (54, -23379840), (67, 4561920), (68, 1520640), (69, 3041280), (79, -280558080), (89, -225815040), (92, 280558080), (96, 140279040), (103, -56453760), (111, 37635840), (112, -46759680), (113, -46759680), (131, 37635840), (143, -18247680), (151, -9123840), (163, -4561920), (175, 13685760), (204, -112907520), (205, 140279040)]

def pairMerged173 : Integer.Sparse (Fin 271) := [(0, -967032), (1, -1976040), (2, 18897120), (3, 198570240), (4, 12545280), (5, -77251680), (6, 14556960), (7, 111386880), (8, 9884160), (9, -10644480), (12, 2217600), (13, 88323840), (23, -7413120), (26, 37635840), (34, 168917760), (50, -30032640), (51, 220239360), (53, -90288000), (58, 19008000), (67, 35038080), (68, 25027200), (69, 10010880), (90, -22809600), (94, -45619200), (95, 225815040), (112, -52462080), (113, -30032640), (133, 15206400), (143, -75271680), (151, -30032640), (163, -18817920), (171, -11404800), (175, 56453760), (194, 112907520), (199, -22809600), (203, -22809600), (204, 112907520), (247, 3801600), (268, -30032640)]

def pairMerged174 : Integer.Sparse (Fin 271) := [(0, -2114640), (1, -40170240), (2, 101106720), (3, 610473600), (4, 71470080), (5, -113699520), (6, 16386480), (7, 82114560), (8, 81354240), (9, -11404800), (12, 101819520), (13, 153711360), (23, -39916800), (24, -9123840), (25, 94089600), (26, 74511360), (32, -374077440), (34, 157322880), (50, -30032640), (51, 304254720), (53, -113097600), (54, -23379840), (58, 19008000), (67, 39600000), (68, 26547840), (69, 13052160), (79, -280558080), (89, -225815040), (90, -22809600), (92, 280558080), (94, -45619200), (95, 225815040), (96, 140279040), (103, -56453760), (111, 37635840), (112, -99221760), (113, -76792320), (131, 37635840), (133, 15206400), (143, -93519360), (151, -39156480), (163, -23379840), (171, -11404800), (175, 70139520), (194, 112907520), (199, -22809600), (203, -22809600), (205, 140279040), (247, 3801600), (268, -30032640)]

def pairMerged175 : Integer.Sparse (Fin 271) := [(0, -709200), (1, 2697120), (2, 3645360), (3, 88093440), (5, -10601280), (6, 2731680), (7, 88842240), (8, 25735680), (9, -6076800), (10, -14135040), (12, 26092800), (13, 22648320), (23, -23397120), (26, 18132480), (27, 10601280), (34, 39709440), (50, -25539840), (51, 2534400), (53, -6531840), (54, -51667200), (58, -7603200), (67, 25574400), (68, 8709120), (69, 16865280), (85, 39191040), (97, 22809600), (111, -40262400), (130, -13063680), (131, -6531840), (143, -46794240), (146, -20666880), (151, -7603200), (163, -10333440), (168, 19595520), (174, 31000320), (203, 22809600), (247, -6531840)]

def pairMerged176 : Integer.Sparse (Fin 271) := [(0, -336384), (1, 2338560), (2, -4772160), (3, -15851520), (4, -9446400), (5, 4688640), (6, -198720), (7, -6635520), (8, -12165120), (9, -115200), (12, 2626560), (13, -92160), (23, -12441600), (24, -13824000), (25, -4147200), (26, -7603200), (27, 3456000), (30, 22809600), (34, -3225600), (42, -13685760), (47, 12441600), (50, 18662400), (54, -8294400), (55, 9123840), (62, -2764800), (66, 1382400), (67, 1382400), (68, 921600), (75, -13685760), (89, -27371520), (99, -27371520), (111, -8294400), (113, -8294400), (130, -2764800), (131, -8294400), (143, 1520640), (148, 15206400), (181, -1382400), (242, 8294400), (252, -9123840), (256, 12441600)]

def pairMerged177 : Integer.Sparse (Fin 271) := [(0, -1045584), (1, 5035680), (2, -1126800), (3, 72241920), (4, -9446400), (5, -5912640), (6, 2532960), (7, 82206720), (8, 13570560), (9, -6192000), (10, -14135040), (12, 28719360), (13, 22556160), (23, -35838720), (24, -13824000), (25, -4147200), (26, 10529280), (27, 14057280), (30, 22809600), (34, 36483840), (42, -13685760), (47, 12441600), (50, -6877440), (51, 2534400), (53, -6531840), (54, -59961600), (55, 9123840), (58, -7603200), (62, -2764800), (66, 1382400), (67, 26956800), (68, 9630720), (69, 16865280), (75, -13685760), (85, 39191040), (89, -27371520), (97, 22809600), (99, -27371520), (111, -48556800), (113, -8294400), (130, -15828480), (131, -14826240), (143, -45273600), (146, -20666880), (148, 15206400), (151, -7603200), (163, -10333440), (168, 19595520), (174, 31000320), (181, -1382400), (203, 22809600), (242, 8294400), (247, -6531840), (252, -9123840), (256, 12441600)]

def pairMerged178 : Integer.Sparse (Fin 271) := [(0, -3160224), (1, -35134560), (2, 99979920), (3, 682715520), (4, 62023680), (5, -119612160), (6, 18919440), (7, 164321280), (8, 94924800), (9, -17596800), (10, -14135040), (12, 130538880), (13, 176267520), (23, -75755520), (24, -22947840), (25, 89942400), (26, 85040640), (27, 14057280), (30, 22809600), (32, -374077440), (34, 193806720), (42, -13685760), (47, 12441600), (50, -36910080), (51, 306789120), (53, -119629440), (54, -83341440), (55, 9123840), (58, 11404800), (62, -2764800), (66, 1382400), (67, 66556800), (68, 36178560), (69, 29917440), (75, -13685760), (79, -280558080), (85, 39191040), (89, -253186560), (90, -22809600), (92, 280558080), (94, -45619200), (95, 225815040), (96, 140279040), (97, 22809600), (99, -27371520), (103, -56453760), (111, -10920960), (112, -99221760), (113, -85086720), (130, -15828480), (131, 22809600), (133, 15206400), (143, -138792960), (146, -20666880), (148, 15206400), (151, -46759680), (163, -33713280), (168, 19595520), (171, -11404800), (174, 31000320), (175, 70139520), (181, -1382400), (194, 112907520), (199, -22809600), (205, 140279040), (242, 8294400), (247, -2730240), (252, -9123840), (256, 12441600), (268, -30032640)]

def pairMerged179 : Integer.Sparse (Fin 271) := [(0, -77376), (1, -6401440), (2, 12177120), (3, 93818880), (4, 23861760), (5, -18446080), (6, 1129920), (7, 46095360), (8, 29644800), (9, -33920), (10, -33350400), (11, 8225280), (12, 16464640), (13, 22233600), (26, 31272960), (32, -4884480), (34, 38113280), (35, 3663360), (37, 33350400), (39, 74027520), (51, 9853440), (53, -1221120), (54, -37013760), (58, -22233600), (67, 407040), (68, 271360), (70, 33350400), (73, 66700800), (132, -3705600), (143, -24675840), (179, -3663360), (185, 7326720), (193, 66700800), (223, 3663360), (229, 22233600), (232, 133401600), (245, -2442240), (246, -407040), (248, -14822400), (249, -1628160), (258, 7326720), (260, 2442240), (262, 14653440)]

def pairMerged180 : Integer.Sparse (Fin 271) := [(0, -91008), (1, -256320), (2, 892800), (3, 783360), (4, -4055040), (5, -311040), (6, -31680), (7, 2995200), (8, 414720), (9, 126720), (10, 1658880), (12, 322560), (13, -184320), (23, 3456000), (24, 5944320), (25, -2764800), (26, -92160), (27, 933120), (32, -2764800), (34, -1105920), (46, -9123840), (50, -13547520), (51, -1013760), (53, -6912000), (54, 7464960), (64, -2764800), (66, -1140480), (67, -1520640), (68, -1013760), (77, -4976640), (87, 4147200), (103, -4561920), (109, 16588800), (111, 1520640), (112, 13685760), (113, 9123840), (114, -1382400), (131, 3041280), (175, -4561920), (177, 8294400), (178, 8294400), (181, 1520640), (234, -9123840), (241, -9123840), (248, 1520640), (256, -4561920)]

def pairMerged181 : Integer.Sparse (Fin 271) := [(0, -168384), (1, -6657760), (2, 13069920), (3, 94602240), (4, 19806720), (5, -18757120), (6, 1098240), (7, 49090560), (8, 30059520), (9, 92800), (10, -31691520), (11, 8225280), (12, 16787200), (13, 22049280), (23, 3456000), (24, 5944320), (25, -2764800), (26, 31180800), (27, 933120), (32, -7649280), (34, 37007360), (35, 3663360), (37, 33350400), (39, 74027520), (46, -9123840), (50, -13547520), (51, 8839680), (53, -8133120), (54, -29548800), (58, -22233600), (64, -2764800), (66, -1140480), (67, -1113600), (68, -742400), (70, 33350400), (73, 66700800), (77, -4976640), (87, 4147200), (103, -4561920), (109, 16588800), (111, 1520640), (112, 13685760), (113, 9123840), (114, -1382400), (131, 3041280), (132, -3705600), (143, -24675840), (175, -4561920), (177, 8294400), (178, 8294400), (179, -3663360), (181, 1520640), (185, 7326720), (193, 66700800), (223, 3663360), (229, 22233600), (232, 133401600), (234, -9123840), (241, -9123840), (245, -2442240), (246, -407040), (248, -13301760), (249, -1628160), (256, -4561920), (258, 7326720), (260, 2442240), (262, 14653440)]

def pairMerged182 : Integer.Sparse (Fin 271) := [(0, -354240), (1, 7585920), (2, -13435200), (3, -53314560), (4, -22855680), (5, 14065920), (6, -910080), (7, -16819200), (8, -29214720), (9, 518400), (12, -4055040), (23, 6082560), (24, 36495360), (26, -8478720), (27, -14446080), (29, 21288960), (30, 24883200), (32, 12165120), (34, -6359040), (45, -19077120), (48, -18247680), (50, 53637120), (51, -7372800), (54, 24330240), (55, 22256640), (66, -2280960), (67, -4193280), (68, -2119680), (69, -8294400), (75, -19077120), (89, -9538560), (97, -9123840), (98, -18247680), (99, -19077120), (111, 3041280), (113, 21288960), (131, 12165120), (143, 6359040), (146, 18247680), (147, 9123840), (148, 9538560), (155, 12718080), (170, -9538560), (174, -9123840), (177, -18247680), (179, 6082560), (181, 3041280), (182, 9538560), (199, -19077120), (249, 3041280), (250, -19077120), (251, -19077120), (256, -9123840), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged183 : Integer.Sparse (Fin 271) := [(0, 131904), (1, 2931840), (2, -538560), (3, -21058560), (4, -3502080), (5, -887040), (6, 305280), (7, -8064000), (8, 5990400), (9, -11520), (12, -5760000), (13, -4147200), (23, 10920960), (24, 6912000), (25, 13824000), (26, -1843200), (27, -864000), (29, -3041280), (30, 11059200), (32, -552960), (34, -5990400), (44, 18247680), (47, -8294400), (50, 5253120), (51, -2672640), (53, 8847360), (54, 5529600), (55, 6912000), (63, 13824000), (66, -1036800), (67, -875520), (68, -921600), (69, 4055040), (89, -4147200), (92, -24883200), (96, -8294400), (111, 1382400), (112, 12441600), (113, 8294400), (131, 2764800), (148, 9676800), (153, -6082560), (168, 4561920), (175, -4147200), (176, 9123840), (178, -8294400), (180, 2764800), (181, -4561920), (182, 1382400), (197, 9123840), (234, -4147200), (238, -8294400), (242, -8294400), (245, -3041280), (246, -1520640), (248, 1382400), (253, 18247680), (254, 18247680)]

def pairMerged184 : Integer.Sparse (Fin 271) := [(0, -222336), (1, 10517760), (2, -13973760), (3, -74373120), (4, -26357760), (5, 13178880), (6, -604800), (7, -24883200), (8, -23224320), (9, 506880), (12, -9815040), (13, -4147200), (23, 17003520), (24, 43407360), (25, 13824000), (26, -10321920), (27, -15310080), (29, 18247680), (30, 35942400), (32, 11612160), (34, -12349440), (44, 18247680), (45, -19077120), (47, -8294400), (48, -18247680), (50, 58890240), (51, -10045440), (53, 8847360), (54, 29859840), (55, 29168640), (63, 13824000), (66, -3317760), (67, -5068800), (68, -3041280), (69, -4239360), (75, -19077120), (89, -13685760), (92, -24883200), (96, -8294400), (97, -9123840), (98, -18247680), (99, -19077120), (111, 4423680), (112, 12441600), (113, 29583360), (131, 14929920), (143, 6359040), (146, 18247680), (147, 9123840), (148, 19215360), (153, -6082560), (155, 12718080), (168, 4561920), (170, -9538560), (174, -9123840), (175, -4147200), (176, 9123840), (177, -18247680), (178, -8294400), (179, 6082560), (180, 2764800), (181, -1520640), (182, 10920960), (197, 9123840), (199, -19077120), (234, -4147200), (238, -8294400), (242, -8294400), (245, -3041280), (246, -1520640), (248, 1382400), (249, 3041280), (250, -19077120), (251, -19077120), (253, 18247680), (254, 18247680), (256, -9123840), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged185 : Integer.Sparse (Fin 271) := [(0, -390720), (1, 3860000), (2, -903840), (3, 20229120), (4, -6551040), (5, -5578240), (6, 493440), (7, 24207360), (8, 6835200), (9, 599680), (10, -31691520), (11, 8225280), (12, 6972160), (13, 17902080), (23, 20459520), (24, 49351680), (25, 11059200), (26, 20858880), (27, -14376960), (29, 18247680), (30, 35942400), (32, 3962880), (34, 24657920), (35, 3663360), (37, 33350400), (39, 74027520), (44, 18247680), (45, -19077120), (46, -9123840), (47, -8294400), (48, -18247680), (50, 45342720), (51, -1205760), (53, 714240), (54, 311040), (55, 29168640), (58, -22233600), (63, 13824000), (64, -2764800), (66, -4458240), (67, -6182400), (68, -3783680), (69, -4239360), (70, 33350400), (73, 66700800), (75, -19077120), (77, -4976640), (87, 4147200), (89, -13685760), (92, -24883200), (96, -8294400), (97, -9123840), (98, -18247680), (99, -19077120), (103, -4561920), (109, 16588800), (111, 5944320), (112, 26127360), (113, 38707200), (114, -1382400), (131, 17971200), (132, -3705600), (143, -18316800), (146, 18247680), (147, 9123840), (148, 19215360), (153, -6082560), (155, 12718080), (168, 4561920), (170, -9538560), (174, -9123840), (175, -8709120), (176, 9123840), (177, -9953280), (179, 2419200), (180, 2764800), (182, 10920960), (185, 7326720), (193, 66700800), (197, 9123840), (199, -19077120), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (242, -8294400), (245, -5483520), (246, -1927680), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (253, 18247680), (254, 18247680), (256, -13685760), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680)]

def pairMerged186 : Integer.Sparse (Fin 271) := [(0, -3550944), (1, -31274560), (2, 99076080), (3, 702944640), (4, 55472640), (5, -125190400), (6, 19412880), (7, 188528640), (8, 101760000), (9, -16997120), (10, -45826560), (11, 8225280), (12, 137511040), (13, 194169600), (23, -55296000), (24, 26403840), (25, 101001600), (26, 105899520), (27, -319680), (29, 18247680), (30, 58752000), (32, -370114560), (34, 218464640), (35, 3663360), (37, 33350400), (39, 74027520), (42, -13685760), (44, 18247680), (45, -19077120), (46, -9123840), (47, 4147200), (48, -18247680), (50, 8432640), (51, 305583360), (53, -118915200), (54, -83030400), (55, 38292480), (58, -10828800), (62, -2764800), (63, 13824000), (64, -2764800), (66, -3075840), (67, 60374400), (68, 32394880), (69, 25678080), (70, 33350400), (73, 66700800), (75, -32762880), (77, -4976640), (79, -280558080), (85, 39191040), (87, 4147200), (89, -266872320), (90, -22809600), (92, 255674880), (94, -45619200), (95, 225815040), (96, 131984640), (97, 13685760), (98, -18247680), (99, -46448640), (103, -61015680), (109, 16588800), (111, -4976640), (112, -73094400), (113, -46379520), (114, -1382400), (130, -15828480), (131, 40780800), (132, -3705600), (133, 15206400), (143, -157109760), (146, -2419200), (147, 9123840), (148, 34421760), (151, -46759680), (153, -6082560), (155, 12718080), (163, -33713280), (168, 24157440), (170, -9538560), (171, -11404800), (174, 21876480), (175, 61430400), (176, 9123840), (177, -9953280), (179, 2419200), (180, 2764800), (181, -1382400), (182, 10920960), (185, 7326720), (193, 66700800), (194, 112907520), (197, 9123840), (199, -41886720), (205, 140279040), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -5483520), (246, -1927680), (247, -2730240), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680), (268, -30032640)]

def pairMerged187 : Integer.Sparse (Fin 271) := [(0, -2779344), (1, -22533240), (2, 97570200), (3, 714168960), (4, 88243200), (5, -140599680), (6, 22933280), (7, 151831680), (8, 98480640), (9, -12135680), (10, -22412160), (11, 21726720), (12, 126280960), (13, 298686720), (23, 26006400), (24, 64696320), (25, 101001600), (26, 183060480), (27, -16411680), (29, 22049280), (30, 105511680), (31, -153600), (32, -357546240), (33, 26449920), (34, 321022080), (35, 3663360), (37, 33350400), (39, 74027520), (42, -13685760), (44, 18247680), (45, -19077120), (46, -9123840), (47, 4147200), (48, -18247680), (50, 63348480), (51, 385040640), (53, -70744320), (54, -42284160), (55, 35942400), (58, -75502080), (59, 26859520), (60, 1382400), (62, -11059200), (63, 13824000), (64, -2764800), (65, 31948800), (66, -3075840), (67, 31223040), (68, 8715520), (69, 21588480), (70, 23811840), (71, -2488320), (72, -40227840), (73, 55296000), (74, 37324800), (75, -106168320), (76, -22809600), (77, -25453440), (79, -227773440), (80, 12687360), (82, 7672320), (83, 30689280), (84, -24468480), (85, 39191040), (87, 4147200), (88, -140279040), (89, -266872320), (90, -22809600), (92, 255674880), (94, -45619200), (95, 225815040), (96, 131984640), (97, 13685760), (98, -18247680), (99, -46448640), (103, -61015680), (109, 16588800), (110, -11059200), (111, 18403200), (112, -73094400), (113, -46379520), (115, 35112960), (130, 7551360), (131, 40780800), (132, -2853120), (133, -11013120), (143, -173076480), (146, -2419200), (147, -1935360), (148, 34421760), (151, -4838400), (153, -6082560), (155, 12718080), (159, -15713280), (160, -24514560), (161, 1105920), (162, 13040640), (163, -31726080), (168, 12337920), (170, 8294400), (171, -2903040), (172, -4147200), (173, -22809600), (174, -19077120), (176, 9123840), (177, -9953280), (179, -3110400), (180, 2764800), (181, -1382400), (182, 10920960), (185, 7326720), (193, 66700800), (194, -8916480), (199, -35665920), (218, -30320640), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -41057280), (246, -1927680), (247, 2937600), (248, -11919360), (249, 1413120), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, 3179520), (266, -18247680), (267, -18247680), (268, 10851840)]

def pairMerged188 : Integer.Sparse (Fin 271) := [(0, -30910440), (1, 174361680), (2, 3379200), (3, 525281280), (4, -336044160), (5, -246632640), (6, 32505680), (7, 123008640), (8, 104862720), (9, -12799040), (10, -2851200), (11, -6503040), (12, 306736000), (13, 754268160), (15, -38776320), (17, -294969600), (18, 82321920), (21, -37324800), (23, -37514880), (24, 274821120), (25, -205562880), (26, -23688960), (27, 31661280), (29, 22049280), (30, 222808320), (31, -153600), (32, -318960000), (33, -1301760), (34, 479364480), (35, 151148160), (36, -71331840), (37, 33350400), (39, 36702720), (42, 104302080), (43, -121305600), (44, -457021440), (45, -177500160), (46, 108864000), (47, 78382080), (48, -18247680), (49, 235975680), (50, -262103040), (51, 448598400), (52, -145981440), (53, -475303680), (54, 46604160), (55, -162570240), (56, -108656640), (57, 1017720), (58, -80478720), (59, 18288640), (60, 1382400), (62, -11059200), (63, -145532160), (64, -2764800), (65, 57200640), (66, 37920960), (67, -83775360), (68, -43917440), (69, -69292800), (70, 23811840), (71, -2488320), (72, -40227840), (73, 55296000), (74, 37324800), (75, -106168320), (76, -22809600), (77, -25453440), (79, -124508160), (80, 75717120), (82, 7672320), (83, 30689280), (84, -24468480), (85, 39191040), (87, 4147200), (88, -140279040), (89, -266872320), (90, -22809600), (91, -294969600), (92, 292792320), (94, -45619200), (95, 225815040), (96, 249972480), (97, 13685760), (98, -18247680), (99, -43130880), (102, 3317760), (103, -61015680), (104, -79211520), (105, -158423040), (107, -145981440), (108, -158423040), (109, 16588800), (110, -22982400), (111, 3732480), (112, -53308800), (113, 57024000), (114, -2488320), (115, 89856000), (117, -225037440), (118, 1658880), (119, -35665920), (122, 117987840), (125, -38776320), (126, -293310720), (127, 164643840), (128, -37324800), (130, 26023680), (131, 130965120), (132, -56110080), (133, -134288640), (135, -37324800), (137, -80870400), (139, 117987840), (140, -294969600), (143, 53585280), (146, -232450560), (147, -27959040), (148, -85916160), (153, -7464960), (154, 17141760), (155, 11335680), (159, -15713280), (160, 14607360), (161, 1105920), (168, 12337920), (170, 8294400), (171, -2903040), (172, -4147200), (173, -22809600), (174, -19077120), (176, 9123840), (177, -9953280), (179, 36011520), (180, 41886720), (181, -2799360), (182, 19215360), (185, 7326720), (193, 66700800), (194, -8916480), (199, -35665920), (218, -30320640), (219, -30758400), (223, 3663360), (229, 22233600), (232, 133401600), (234, -13271040), (238, -8294400), (241, -9123840), (245, -41057280), (246, -19680000), (248, 61831680), (249, 55833600), (250, -19077120), (251, -19077120), (252, -9123840), (253, 18247680), (254, 18247680), (256, -1244160), (258, 7326720), (260, 2442240), (262, 14653440), (263, -81838080), (266, -18247680), (267, -18247680)]

def pairMerged189 : Integer.Sparse (Fin 271) := [(0, 513792), (1, -7562880), (2, 403200), (3, -15298560), (4, 3271680), (5, 2914560), (6, -984960), (7, 13685760), (8, 10506240), (9, 34560), (10, -6082560), (11, -2304000), (12, -7557120), (13, -36218880), (24, -24330240), (26, 368640), (27, 6842880), (29, -12165120), (30, -12165120), (34, -17326080), (44, -20736000), (48, 18247680), (50, 276480), (51, -37140480), (53, 13824000), (54, -21288960), (55, 13824000), (66, 2280960), (67, -2442240), (68, -2304000), (69, -552960), (80, 2027520), (88, 18247680), (94, -41472000), (95, -20736000), (99, 36495360), (111, -3041280), (113, -21288960), (131, -12165120), (143, 6912000), (146, -18247680), (148, -12165120), (155, 13824000), (170, -10368000), (174, 9123840), (182, 7326720), (199, -20736000), (234, 9123840), (249, -3041280), (254, -20736000), (263, 3456000), (265, 18247680), (266, 18247680), (270, -20736000)]

def pairMerged190 : Integer.Sparse (Fin 271) := [(0, 536736), (1, -9680640), (2, -13080480), (3, -47162880), (4, 8110080), (5, 23237760), (6, -3430080), (7, -21265920), (8, -8908800), (9, 405120), (10, 14584320), (11, 1520640), (12, -17817600), (13, -59535360), (26, 9123840), (32, 19445760), (34, -38169600), (37, -29168640), (42, 9123840), (44, 9123840), (50, -7603200), (51, -45864960), (53, 13363200), (54, -1520640), (55, -6082560), (58, 19445760), (67, -4861440), (68, -3240960), (70, -14584320), (73, -29168640), (75, 4561920), (80, -16204800), (94, 18247680), (95, 18247680), (115, -16204800), (132, 14584320), (133, 38891520), (143, -6082560), (179, 14584320), (186, -58337280), (223, -14584320), (229, -29168640), (236, -29168640), (240, 9123840), (245, 19445760), (246, 4861440), (252, 9123840), (254, 9123840), (258, -29168640), (270, 9123840)]

def pairMerged191 : Integer.Sparse (Fin 271) := [(0, 1050528), (1, -17243520), (2, -12677280), (3, -62461440), (4, 11381760), (5, 26152320), (6, -4415040), (7, -7580160), (8, 1597440), (9, 439680), (10, 8501760), (11, -783360), (12, -25374720), (13, -95754240), (24, -24330240), (26, 9492480), (27, 6842880), (29, -12165120), (30, -12165120), (32, 19445760), (34, -55495680), (37, -29168640), (42, 9123840), (44, -11612160), (48, 18247680), (50, -7326720), (51, -83005440), (53, 27187200), (54, -22809600), (55, 7741440), (58, 19445760), (66, 2280960), (67, -7303680), (68, -5544960), (69, -552960), (70, -14584320), (73, -29168640), (75, 4561920), (80, -14177280), (88, 18247680), (94, -23224320), (95, -2488320), (99, 36495360), (111, -3041280), (113, -21288960), (115, -16204800), (131, -12165120), (132, 14584320), (133, 38891520), (143, 829440), (146, -18247680), (148, -12165120), (155, 13824000), (170, -10368000), (174, 9123840), (179, 14584320), (182, 7326720), (186, -58337280), (199, -20736000), (223, -14584320), (229, -29168640), (234, 9123840), (236, -29168640), (240, 9123840), (245, 19445760), (246, 4861440), (249, -3041280), (252, 9123840), (254, -11612160), (258, -29168640), (263, 3456000), (265, 18247680), (266, 18247680), (270, -11612160)]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

def pairMerged192 : Integer.Sparse (Fin 271) := [(0, 37632), (1, -247680), (2, -23040), (3, 1935360), (4, 2304000), (5, 576000), (6, -63360), (7, -1843200), (9, 84480), (12, 460800), (13, 1597440), (23, -829440), (24, -9953280), (25, -3594240), (27, -391680), (32, -552960), (34, -552960), (50, 9123840), (53, 12165120), (54, -13271040), (62, -2396160), (66, -230400), (67, -1013760), (68, -675840), (111, 2764800), (113, -3317760), (130, 1843200), (131, -6635520), (153, 6082560), (168, -9123840), (174, 9953280), (176, -9123840), (177, 9953280), (179, -3317760), (181, 3041280), (245, 3041280), (246, 3041280), (249, -3317760)]

def pairMerged193 : Integer.Sparse (Fin 271) := [(0, 194880), (1, 9183360), (2, -2764800), (3, -112788480), (4, -25712640), (5, -3367680), (6, 502080), (7, -8939520), (8, 11796480), (9, -599040), (10, 20044800), (12, -53283840), (13, -77783040), (24, -25159680), (25, 40089600), (26, -31703040), (27, 7188480), (29, -7188480), (30, 5667840), (32, 40089600), (34, -44728320), (37, -60134400), (38, -120268800), (45, 10782720), (50, -19491840), (51, -31534080), (53, 60134400), (54, 12856320), (55, -7188480), (58, 40089600), (59, -8908800), (66, 1797120), (67, 7188480), (68, 3594240), (69, 5990400), (79, 40089600), (80, -6681600), (82, -60134400), (83, -120268800), (88, 21565440), (98, 10782720), (99, 21565440), (113, -21565440), (115, -13363200), (131, -7188480), (143, 60134400), (146, -7188480), (147, -3594240), (148, -7188480), (155, -7188480), (181, -3594240), (182, -3594240), (184, -60134400), (193, -120268800), (194, 10782720), (195, -40089600), (199, 10782720), (201, -120268800), (202, -120268800), (218, 20044800), (219, 26726400), (250, 21565440), (251, 10782720), (253, 10782720)]

def pairMerged194 : Integer.Sparse (Fin 271) := [(0, 232512), (1, 8935680), (2, -2787840), (3, -110853120), (4, -23408640), (5, -2791680), (6, 438720), (7, -10782720), (8, 11796480), (9, -514560), (10, 20044800), (12, -52823040), (13, -76185600), (23, -829440), (24, -35112960), (25, 36495360), (26, -31703040), (27, 6796800), (29, -7188480), (30, 5667840), (32, 39536640), (34, -45281280), (37, -60134400), (38, -120268800), (45, 10782720), (50, -10368000), (51, -31534080), (53, 72299520), (54, -414720), (55, -7188480), (58, 40089600), (59, -8908800), (62, -2396160), (66, 1566720), (67, 6174720), (68, 2918400), (69, 5990400), (79, 40089600), (80, -6681600), (82, -60134400), (83, -120268800), (88, 21565440), (98, 10782720), (99, 21565440), (111, 2764800), (113, -24883200), (115, -13363200), (130, 1843200), (131, -13824000), (143, 60134400), (146, -7188480), (147, -3594240), (148, -7188480), (153, 6082560), (155, -7188480), (168, -9123840), (174, 9953280), (176, -9123840), (177, 9953280), (179, -3317760), (181, -552960), (182, -3594240), (184, -60134400), (193, -120268800), (194, 10782720), (195, -40089600), (199, 10782720), (201, -120268800), (202, -120268800), (218, 20044800), (219, 26726400), (245, 3041280), (246, 3041280), (249, -3317760), (250, 21565440), (251, 10782720), (253, 10782720)]

def pairMerged195 : Integer.Sparse (Fin 271) := [(0, 1283040), (1, -8307840), (2, -15465120), (3, -173314560), (4, -12026880), (5, 23360640), (6, -3976320), (7, -18362880), (8, 13393920), (9, -74880), (10, 28546560), (11, -783360), (12, -78197760), (13, -171939840), (23, -829440), (24, -59443200), (25, 36495360), (26, -22210560), (27, 13639680), (29, -19353600), (30, -6497280), (32, 58982400), (34, -100776960), (37, -89303040), (38, -120268800), (42, 9123840), (44, -11612160), (45, 10782720), (48, 18247680), (50, -17694720), (51, -114539520), (53, 99486720), (54, -23224320), (55, 552960), (58, 59535360), (59, -8908800), (62, -2396160), (66, 3847680), (67, -1128960), (68, -2626560), (69, 5437440), (70, -14584320), (73, -29168640), (75, 4561920), (79, 40089600), (80, -20858880), (82, -60134400), (83, -120268800), (88, 39813120), (94, -23224320), (95, -2488320), (98, 10782720), (99, 58060800), (111, -276480), (113, -46172160), (115, -29568000), (130, 1843200), (131, -25989120), (132, 14584320), (133, 38891520), (143, 60963840), (146, -25436160), (147, -3594240), (148, -19353600), (153, 6082560), (155, 6635520), (168, -9123840), (170, -10368000), (174, 19077120), (176, -9123840), (177, 9953280), (179, 11266560), (181, -552960), (182, 3732480), (184, -60134400), (186, -58337280), (193, -120268800), (194, 10782720), (195, -40089600), (199, -9953280), (201, -120268800), (202, -120268800), (218, 20044800), (219, 26726400), (223, -14584320), (229, -29168640), (234, 9123840), (236, -29168640), (240, 9123840), (245, 22487040), (246, 7902720), (249, -6359040), (250, 21565440), (251, 10782720), (252, 9123840), (253, 10782720), (254, -11612160), (258, -29168640), (263, 3456000), (265, 18247680), (266, 18247680), (270, -11612160)]

def pairMerged196 : Integer.Sparse (Fin 271) := [(0, -562464), (1, 19544160), (2, -9535520), (3, -170795520), (4, -73666560), (5, 16077440), (6, -879840), (7, -52646400), (8, -25712640), (9, 33920), (10, 19284480), (11, -6835200), (12, -14077440), (13, -17141760), (23, 1221120), (25, 2442240), (26, -84380160), (27, -305280), (30, 2442240), (32, 4884480), (34, -55467520), (35, -3663360), (36, -57853440), (38, -7326720), (39, -115706880), (50, 2442240), (51, -7649280), (53, 6105600), (54, 20505600), (55, 57853440), (66, -101760), (67, -407040), (68, -271360), (79, 38568960), (80, -6428160), (81, -57853440), (83, -115706880), (85, -3663360), (110, 2442240), (111, 1221120), (130, 814080), (142, 1221120), (143, 84787200), (147, 1221120), (153, 2442240), (168, -3663360), (179, 2442240), (181, 1221120), (185, -3663360), (188, -7326720), (223, -7326720), (226, -115706880), (231, -7326720), (232, -115706880), (245, 3663360), (246, 2849280), (249, 407040), (259, -7326720), (260, -2442240), (261, -38568960), (262, -115706880), (263, 25712640)]

def pairMerged197 : Integer.Sparse (Fin 271) := [(0, 52608), (1, -6287520), (2, 7962720), (3, 100584960), (4, 34083840), (5, -11961600), (6, 1130880), (7, 38745600), (8, 8770560), (9, -49920), (11, 8970240), (24, -599040), (26, 59596800), (27, 149760), (30, -599040), (32, -1198080), (34, 61593600), (36, 1797120), (50, -599040), (51, 26688000), (52, 18385920), (54, -599040), (65, 8171520), (66, 74880), (67, 798720), (68, 599040), (79, -44098560), (81, 10091520), (82, 27578880), (83, 38568960), (91, 1797120), (110, -599040), (111, -299520), (113, -599040), (131, -599040), (143, -56286720), (147, -599040), (153, -599040), (179, -1198080), (181, -599040), (185, 898560), (188, 1797120), (194, 1797120), (215, 18385920), (233, 3594240), (237, 1797120), (243, 18385920), (244, 36771840), (245, -898560), (249, -299520), (261, 1797120)]

def pairMerged198 : Integer.Sparse (Fin 271) := [(0, -509856), (1, 13256640), (2, -1572800), (3, -70210560), (4, -39582720), (5, 4115840), (6, 251040), (7, -13900800), (8, -16942080), (9, -16000), (10, 19284480), (11, 2135040), (12, -14077440), (13, -17141760), (23, 1221120), (24, -599040), (25, 2442240), (26, -24783360), (27, -155520), (30, 1843200), (32, 3686400), (34, 6126080), (35, -3663360), (36, -56056320), (38, -7326720), (39, -115706880), (50, 1843200), (51, 19038720), (52, 18385920), (53, 6105600), (54, 19906560), (55, 57853440), (65, 8171520), (66, -26880), (67, 391680), (68, 327680), (79, -5529600), (80, -6428160), (81, -47761920), (82, 27578880), (83, -77137920), (85, -3663360), (91, 1797120), (110, 1843200), (111, 921600), (113, -599040), (130, 814080), (131, -599040), (142, 1221120), (143, 28500480), (147, 622080), (153, 1843200), (168, -3663360), (179, 1244160), (181, 622080), (185, -2764800), (188, -5529600), (194, 1797120), (215, 18385920), (223, -7326720), (226, -115706880), (231, -7326720), (232, -115706880), (233, 3594240), (237, 1797120), (243, 18385920), (244, 36771840), (245, 2764800), (246, 2849280), (249, 107520), (259, -7326720), (260, -2442240), (261, -36771840), (262, -115706880), (263, 25712640)]

def pairMerged199 : Integer.Sparse (Fin 271) := [(0, -814656), (1, -17196480), (2, 39153600), (3, 377472000), (4, 99333120), (5, -65591040), (6, 5837760), (7, 144445440), (8, 72038400), (10, -76861440), (11, 20981760), (12, 77982720), (13, 106214400), (25, -12810240), (26, 135168000), (32, -75755520), (34, 204426240), (36, 113633280), (38, 113633280), (39, 113633280), (51, 95815680), (53, -31196160), (54, -113633280), (55, -37877760), (58, -76861440), (65, 17080320), (71, 76861440), (72, 76861440), (73, 76861440), (79, -101376000), (80, 8171520), (81, 18385920), (82, 38430720), (83, 113633280), (115, 8171520), (132, -6128640), (133, -25067520), (143, -125890560), (179, -36771840), (180, -38430720), (185, 36771840), (193, 76861440), (201, 73543680), (202, 153722880), (211, 38430720), (213, 76861440), (225, 36771840), (226, 153722880), (228, 76861440), (231, 76861440), (232, 230584320), (233, 36771840), (237, 73543680), (245, -12257280), (248, -51240960), (249, -24514560), (258, 36771840), (259, 36771840), (261, 36771840), (262, 110315520)]

def pairMerged200 : Integer.Sparse (Fin 271) := [(0, 308736), (1, -6788160), (2, 14872320), (3, 57231360), (4, 17418240), (5, -17544960), (6, 1454400), (7, 28938240), (8, 19584000), (9, -702720), (12, 5437440), (13, 10782720), (23, -23086080), (24, -60825600), (26, 3225600), (27, 20977920), (29, -24330240), (30, -18247680), (34, 27002880), (37, 5391360), (46, 9123840), (50, -9123840), (51, 26219520), (53, -1797120), (54, -35251200), (58, -5391360), (59, 4193280), (66, 3490560), (67, 8017920), (68, 4008960), (69, 2027520), (79, -7188480), (80, 599040), (82, 10782720), (90, 5391360), (98, 36495360), (112, -17556480), (113, -34007040), (115, 2995200), (131, -6082560), (133, -1797120), (143, -3594240), (146, -12165120), (147, -13962240), (154, -3594240), (171, 5391360), (179, -3594240), (181, -4838400), (195, 10782720), (207, 5391360), (219, -1797120), (224, 10782720), (234, 18247680), (236, 5391360), (237, 10782720), (241, 9123840), (249, -1797120), (267, 18247680)]

def pairMerged201 : Integer.Sparse (Fin 271) := [(0, -505920), (1, -23984640), (2, 54025920), (3, 434703360), (4, 116751360), (5, -83136000), (6, 7292160), (7, 173383680), (8, 91622400), (9, -702720), (10, -76861440), (11, 20981760), (12, 83420160), (13, 116997120), (23, -23086080), (24, -60825600), (25, -12810240), (26, 138393600), (27, 20977920), (29, -24330240), (30, -18247680), (32, -75755520), (34, 231429120), (36, 113633280), (37, 5391360), (38, 113633280), (39, 113633280), (46, 9123840), (50, -9123840), (51, 122035200), (53, -32993280), (54, -148884480), (55, -37877760), (58, -82252800), (59, 4193280), (65, 17080320), (66, 3490560), (67, 8017920), (68, 4008960), (69, 2027520), (71, 76861440), (72, 76861440), (73, 76861440), (79, -108564480), (80, 8770560), (81, 18385920), (82, 49213440), (83, 113633280), (90, 5391360), (98, 36495360), (112, -17556480), (113, -34007040), (115, 11166720), (131, -6082560), (132, -6128640), (133, -26864640), (143, -129484800), (146, -12165120), (147, -13962240), (154, -3594240), (171, 5391360), (179, -40366080), (180, -38430720), (181, -4838400), (185, 36771840), (193, 76861440), (195, 10782720), (201, 73543680), (202, 153722880), (207, 5391360), (211, 38430720), (213, 76861440), (219, -1797120), (224, 10782720), (225, 36771840), (226, 153722880), (228, 76861440), (231, 76861440), (232, 230584320), (233, 36771840), (234, 18247680), (236, 5391360), (237, 84326400), (241, 9123840), (245, -12257280), (248, -51240960), (249, -26311680), (258, 36771840), (259, 36771840), (261, 36771840), (262, 110315520), (267, 18247680)]

def pairMerged202 : Integer.Sparse (Fin 271) := [(0, -1015776), (1, -10728000), (2, 52453120), (3, 364492800), (4, 77168640), (5, -79020160), (6, 7543200), (7, 159482880), (8, 74680320), (9, -718720), (10, -57576960), (11, 23116800), (12, 69342720), (13, 99855360), (23, -21864960), (24, -61424640), (25, -10368000), (26, 113610240), (27, 20822400), (29, -24330240), (30, -16404480), (32, -72069120), (34, 237555200), (35, -3663360), (36, 57576960), (37, 5391360), (38, 106306560), (39, -2073600), (46, 9123840), (50, -7280640), (51, 141073920), (52, 18385920), (53, -26887680), (54, -128977920), (55, 19975680), (58, -82252800), (59, 4193280), (65, 25251840), (66, 3463680), (67, 8409600), (68, 4336640), (69, 2027520), (71, 76861440), (72, 76861440), (73, 76861440), (79, -114094080), (80, 2342400), (81, -29376000), (82, 76792320), (83, 36495360), (85, -3663360), (90, 5391360), (91, 1797120), (98, 36495360), (110, 1843200), (111, 921600), (112, -17556480), (113, -34606080), (115, 11166720), (130, 814080), (131, -6681600), (132, -6128640), (133, -26864640), (142, 1221120), (143, -100984320), (146, -12165120), (147, -13340160), (153, 1843200), (154, -3594240), (168, -3663360), (171, 5391360), (179, -39121920), (180, -38430720), (181, -4216320), (185, 34007040), (188, -5529600), (193, 76861440), (194, 1797120), (195, 10782720), (201, 73543680), (202, 153722880), (207, 5391360), (211, 38430720), (213, 76861440), (215, 18385920), (219, -1797120), (223, -7326720), (224, 10782720), (225, 36771840), (226, 38016000), (228, 76861440), (231, 69534720), (232, 114877440), (233, 40366080), (234, 18247680), (236, 5391360), (237, 86123520), (241, 9123840), (243, 18385920), (244, 36771840), (245, -9492480), (246, 2849280), (248, -51240960), (249, -26204160), (258, 36771840), (259, 29445120), (260, -2442240), (262, -5391360), (263, 25712640), (267, 18247680)]

def pairMerged203 : Integer.Sparse (Fin 271) := [(0, 267264), (1, -19035840), (2, 36988000), (3, 191178240), (4, 65141760), (5, -55659520), (6, 3566880), (7, 141120000), (8, 88074240), (9, -793600), (10, -29030400), (11, 22333440), (12, -8855040), (13, -72084480), (23, -22694400), (24, -120867840), (25, 26127360), (26, 91399680), (27, 34462080), (29, -43683840), (30, -22901760), (32, -13086720), (34, 136778240), (35, -3663360), (36, 57576960), (37, -83911680), (38, -13962240), (39, -2073600), (42, 9123840), (44, -11612160), (45, 10782720), (46, 9123840), (48, 18247680), (50, -24975360), (51, 26534400), (52, 18385920), (53, 72599040), (54, -152202240), (55, 20528640), (58, -22717440), (59, -4715520), (62, -2396160), (65, 25251840), (66, 7311360), (67, 7280640), (68, 1710080), (69, 7464960), (70, -14584320), (71, 76861440), (72, 76861440), (73, 47692800), (75, 4561920), (79, -74004480), (80, -18516480), (81, -29376000), (82, 16657920), (83, -83773440), (85, -3663360), (88, 39813120), (90, 5391360), (91, 1797120), (94, -23224320), (95, -2488320), (98, 47278080), (99, 58060800), (110, 1843200), (111, 645120), (112, -17556480), (113, -80778240), (115, -18401280), (130, 2657280), (131, -32670720), (132, 8455680), (133, 12026880), (142, 1221120), (143, -40020480), (146, -37601280), (147, -16934400), (148, -19353600), (153, 7925760), (154, -3594240), (155, 6635520), (168, -12787200), (170, -10368000), (171, 5391360), (174, 19077120), (176, -9123840), (177, 9953280), (179, -27855360), (180, -38430720), (181, -4769280), (182, 3732480), (184, -60134400), (185, 34007040), (186, -58337280), (188, -5529600), (193, -43407360), (194, 12579840), (195, -29306880), (199, -9953280), (201, -46725120), (202, 33454080), (207, 5391360), (211, 38430720), (213, 76861440), (215, 18385920), (218, 20044800), (219, 24929280), (223, -21911040), (224, 10782720), (225, 36771840), (226, 38016000), (228, 76861440), (229, -29168640), (231, 69534720), (232, 114877440), (233, 40366080), (234, 27371520), (236, -23777280), (237, 86123520), (240, 9123840), (241, 9123840), (243, 18385920), (244, 36771840), (245, 12994560), (246, 10752000), (248, -51240960), (249, -32563200), (250, 21565440), (251, 10782720), (252, 9123840), (253, 10782720), (254, -11612160), (258, 7603200), (259, 29445120), (260, -2442240), (262, -5391360), (263, 29168640), (265, 18247680), (266, 18247680), (267, 18247680), (270, -11612160)]

def pairMerged204 : Integer.Sparse (Fin 271) := [(0, -413952), (1, -11496960), (2, 894720), (3, 100823040), (4, 2641920), (5, 6758400), (6, -1681920), (7, 31395840), (8, -2088960), (10, -50503680), (11, -921600), (12, 54743040), (13, 77598720), (23, -5345280), (26, 5283840), (27, 1336320), (32, -15851520), (33, 7127040), (34, 36802560), (37, 32071680), (40, -8294400), (50, -21381120), (51, -430080), (53, -13086720), (54, -10690560), (58, -52715520), (59, 6881280), (70, 16035840), (71, 7741440), (72, 23777280), (73, 23777280), (79, 5529600), (80, 3194880), (82, 23777280), (115, -1413120), (132, -4976640), (133, 3317760), (143, -5160960), (160, -10690560), (179, 8294400), (184, 64143360), (186, 47554560), (191, 32071680), (196, -16588800), (207, -8294400), (209, -8294400), (225, -8294400), (227, -16588800), (233, -8294400), (239, -8294400), (245, 5529600), (258, -8294400)]

def pairMerged205 : Integer.Sparse (Fin 271) := [(0, -328464), (1, 38436960), (2, -26780160), (3, -430302720), (4, -157524480), (5, 29268480), (6, -3149520), (7, -89022720), (8, -16289280), (10, 3617280), (11, -27164160), (12, -50073600), (13, -57922560), (23, 3617280), (25, 7234560), (26, -196154880), (27, -904320), (30, 7234560), (32, 43407360), (33, -4823040), (34, -188920320), (35, -21703680), (36, -81492480), (38, -43407360), (39, -162984960), (50, 14469120), (51, -79672320), (53, 36172800), (54, 110430720), (55, 81492480), (58, 14469120), (65, -9054720), (70, -10851840), (71, -40746240), (72, -21703680), (73, -81492480), (79, 110430720), (81, -21703680), (82, -81492480), (83, -206392320), (132, 10851840), (133, 40746240), (143, 191923200), (160, 7234560), (184, -21703680), (185, -43407360), (187, -43407360), (189, -21703680), (193, -21703680), (201, -43407360), (202, -86814720), (218, 21703680), (219, 14469120), (226, -81492480), (228, -81492480), (232, -325969920), (237, -162984960), (262, -162984960), (263, 54328320)]

def pairMerged206 : Integer.Sparse (Fin 271) := [(0, -742416), (1, 26940000), (2, -25885440), (3, -329479680), (4, -154882560), (5, 36026880), (6, -4831440), (7, -57626880), (8, -18378240), (10, -46886400), (11, -28085760), (12, 4669440), (13, 19676160), (23, -1728000), (25, 7234560), (26, -190871040), (27, 432000), (30, 7234560), (32, 27555840), (33, 2304000), (34, -152117760), (35, -21703680), (36, -81492480), (37, 32071680), (38, -43407360), (39, -162984960), (40, -8294400), (50, -6912000), (51, -80102400), (53, 23086080), (54, 99740160), (55, 81492480), (58, -38246400), (59, 6881280), (65, -9054720), (70, 5184000), (71, -33004800), (72, 2073600), (73, -57715200), (79, 115960320), (80, 3194880), (81, -21703680), (82, -57715200), (83, -206392320), (115, -1413120), (132, 5875200), (133, 44064000), (143, 186762240), (160, -3456000), (179, 8294400), (184, 42439680), (185, -43407360), (186, 47554560), (187, -43407360), (189, -21703680), (191, 32071680), (193, -21703680), (196, -16588800), (201, -43407360), (202, -86814720), (207, -8294400), (209, -8294400), (218, 21703680), (219, 14469120), (225, -8294400), (226, -81492480), (227, -16588800), (228, -81492480), (232, -325969920), (233, -8294400), (237, -162984960), (239, -8294400), (245, 5529600), (258, -8294400), (262, -162984960), (263, 54328320)]

def pairMerged207 : Integer.Sparse (Fin 271) := [(0, 84480), (1, 714240), (2, -2304000), (3, -23224320), (4, -4915200), (5, 3379200), (6, 276480), (7, -27770880), (8, -8110080), (10, 1474560), (11, 2211840), (12, 3440640), (13, 6881280), (23, 1474560), (24, 5160960), (25, -3686400), (26, -13025280), (27, -368640), (30, -4423680), (32, -4423680), (34, -28139520), (37, -1105920), (38, 13271040), (50, -1474560), (51, -3194880), (53, -6635520), (54, 5160960), (55, -2211840), (58, 737280), (63, 10321920), (65, -8601600), (70, -4423680), (71, -15482880), (72, 6635520), (79, 20643840), (80, 1474560), (82, -15482880), (85, 6635520), (86, 13271040), (96, -15482880), (110, -8847360), (115, 1474560), (132, -1843200), (133, -2211840), (142, -6635520), (143, -1474560), (147, -2211840), (159, 5160960), (179, -2211840), (186, 6635520), (188, 13271040), (191, -15482880), (211, -15482880), (223, 6635520), (224, -15482880), (229, 6635520), (231, 26542080), (236, 13271040), (245, -6635520), (246, -4423680), (259, 13271040)]

def pairMerged208 : Integer.Sparse (Fin 271) := [(0, 51840), (1, 3648000), (2, -4051200), (3, -66508800), (4, -22579200), (5, 3955200), (6, 67200), (7, -31795200), (8, -6604800), (10, -1382400), (11, -4915200), (12, 768000), (13, 3840000), (24, -1382400), (26, -42086400), (27, 345600), (30, -2764800), (32, 3686400), (33, -4300800), (34, -42393600), (36, -9676800), (40, 4147200), (50, -5529600), (51, -7372800), (55, 460800), (58, -5529600), (59, 921600), (65, -8601600), (71, -5529600), (79, 35942400), (80, 460800), (81, -9676800), (82, -15206400), (83, -30412800), (91, 8294400), (95, 8294400), (110, -5529600), (115, 1382400), (133, 1843200), (143, 40089600), (147, -2764800), (161, 6451200), (179, -2764800), (186, 4147200), (188, 8294400), (190, -19353600), (196, 8294400), (213, -19353600), (215, -19353600), (227, 4147200), (233, -11059200), (239, 8294400), (244, -19353600), (245, -4147200)]

def pairMerged209 : Integer.Sparse (Fin 271) := [(0, 136320), (1, 4362240), (2, -6355200), (3, -89733120), (4, -27494400), (5, 7334400), (6, 343680), (7, -59566080), (8, -14714880), (10, 92160), (11, -2703360), (12, 4208640), (13, 10721280), (23, 1474560), (24, 3778560), (25, -3686400), (26, -55111680), (27, -23040), (30, -7188480), (32, -737280), (33, -4300800), (34, -70533120), (36, -9676800), (37, -1105920), (38, 13271040), (40, 4147200), (50, -7004160), (51, -10567680), (53, -6635520), (54, 5160960), (55, -1751040), (58, -4792320), (59, 921600), (63, 10321920), (65, -17203200), (70, -4423680), (71, -21012480), (72, 6635520), (79, 56586240), (80, 1935360), (81, -9676800), (82, -30689280), (83, -30412800), (85, 6635520), (86, 13271040), (91, 8294400), (95, 8294400), (96, -15482880), (110, -14376960), (115, 2856960), (132, -1843200), (133, -368640), (142, -6635520), (143, 38615040), (147, -4976640), (159, 5160960), (161, 6451200), (179, -4976640), (186, 10782720), (188, 21565440), (190, -19353600), (191, -15482880), (196, 8294400), (211, -15482880), (213, -19353600), (215, -19353600), (223, 6635520), (224, -15482880), (227, 4147200), (229, 6635520), (231, 26542080), (233, -11059200), (236, 13271040), (239, 8294400), (244, -19353600), (245, -10782720), (246, -4423680), (259, 13271040)]

def pairMerged210 : Integer.Sparse (Fin 271) := [(0, -606096), (1, 31302240), (2, -32240640), (3, -419212800), (4, -182376960), (5, 43361280), (6, -4487760), (7, -117192960), (8, -33093120), (10, -46794240), (11, -30789120), (12, 8878080), (13, 30397440), (23, -253440), (24, 3778560), (25, 3548160), (26, -245982720), (27, 408960), (30, 46080), (32, 26818560), (33, -1996800), (34, -222650880), (35, -21703680), (36, -91169280), (37, 30965760), (38, -30136320), (39, -162984960), (40, -4147200), (50, -13916160), (51, -90670080), (53, 16450560), (54, 104901120), (55, 79741440), (58, -43038720), (59, 7802880), (63, 10321920), (65, -26257920), (70, 760320), (71, -54017280), (72, 8709120), (73, -57715200), (79, 172546560), (80, 5130240), (81, -31380480), (82, -88404480), (83, -236805120), (85, 6635520), (86, 13271040), (91, 8294400), (95, 8294400), (96, -15482880), (110, -14376960), (115, 1443840), (132, 4032000), (133, 43695360), (142, -6635520), (143, 225377280), (147, -4976640), (159, 5160960), (160, -3456000), (161, 6451200), (179, 3317760), (184, 42439680), (185, -43407360), (186, 58337280), (187, -43407360), (188, 21565440), (189, -21703680), (190, -19353600), (191, 16588800), (193, -21703680), (196, -8294400), (201, -43407360), (202, -86814720), (207, -8294400), (209, -8294400), (211, -15482880), (213, -19353600), (215, -19353600), (218, 21703680), (219, 14469120), (223, 6635520), (224, -15482880), (225, -8294400), (226, -81492480), (227, -12441600), (228, -81492480), (229, 6635520), (231, 26542080), (232, -325969920), (233, -19353600), (236, 13271040), (237, -162984960), (244, -19353600), (245, -5253120), (246, -4423680), (258, -8294400), (259, 13271040), (262, -162984960), (263, 54328320)]

end MUB6.Certificate.PairData

end OAI
end


