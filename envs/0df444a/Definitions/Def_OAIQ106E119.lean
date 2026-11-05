-- Prove2me | Definitions.Def_OAIQ106E119
-- name    : OAIQ106E119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:26:39.708227+00:00
-- url     : https://prove2.me/theorems/e876963f-2137-41a6-9a7f-1ed9bcabed74
-- title:
--   Definitions bundle OAIQ106E119 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6389 declarations of OpenAI's Lean: 6389 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw9657step3`, `OAI.MUB6.Certificate.MixedSemantics.raw9657step4`, `OAI.MUB6.Certificate.MixedSemantics.raw9657step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9658`, `OAI.MUB6.Certificate.MixedSemantics.raw9658Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9658step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9659`, `OAI.MUB6.Certificate.MixedSemantics.raw9659Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9659step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw965Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw965step0`, `OAI.MUB6.Certificate.MixedSemantics.raw965step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw965step1`, `OAI.MUB6.Certificate.MixedSemantics.raw965step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw965step2`, `OAI.MUB6.Certificate.MixedSemantics.raw965step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw966`, `OAI.MUB6.Certificate.MixedSemantics.raw9660`, `OAI.MUB6.Certificate.MixedSemantics.raw9660Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step0`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step1`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step2`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step3`, `OAI.MUB6.Certificate.MixedSemantics.raw9660step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9661`, `OAI.MUB6.Certificate.MixedSemantics.raw9661Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw9661step0` and 6349 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical7`, `MutuallyUnbiased_MixedSemantics_Canonical75`, `MutuallyUnbiased_MixedSemantics_Canonical76`, `MutuallyUnbiased_MixedSemantics_Canonical77`, `MutuallyUnbiased_MixedSemantics_Canonical78`, `MutuallyUnbiased_MixedSemantics_Singletons10`, `MutuallyUnbiased_MixedSemantics_Singletons18`, `MutuallyUnbiased_MixedSemantics_Singletons19`, `MutuallyUnbiased_MixedSemantics_Singletons20`, `MutuallyUnbiased_MixedSemantics_Singletons21`, `MutuallyUnbiased_MixedSemantics_Singletons22`, `MutuallyUnbiased_MixedSemantics_Singletons23`, `MutuallyUnbiased_MixedSemantics_Singletons36`, `MutuallyUnbiased_MixedSemantics_Singletons39`, `MutuallyUnbiased_MixedSemantics_Singletons40`, `MutuallyUnbiased_MixedSemantics_Singletons41`, `MutuallyUnbiased_MixedSemantics_Singletons43`, `MutuallyUnbiased_MixedSemantics_Singletons44`, `MutuallyUnbiased_MixedSemantics_Singletons45`, `MutuallyUnbiased_MixedSemantics_Singletons46`, `MutuallyUnbiased_MixedSemantics_Singletons48`, `MutuallyUnbiased_MixedSemantics_Singletons49`, `MutuallyUnbiased_MixedSemantics_Singletons50`, `MutuallyUnbiased_MixedSemantics_Singletons57`, `MutuallyUnbiased_MixedSemantics_Singletons58`, `MutuallyUnbiased_MixedSemantics_Singletons59`, `MutuallyUnbiased_MixedSemantics_Singletons60`, `MutuallyUnbiased_MixedSemantics_Singletons61`, `MutuallyUnbiased_MixedSemantics_Singletons62`, `MutuallyUnbiased_MixedSemantics_Singletons63`, `MutuallyUnbiased_MixedSemantics_Singletons64`, `MutuallyUnbiased_MixedSemantics_Singletons65`, `MutuallyUnbiased_MixedSemantics_Singletons66`, `MutuallyUnbiased_MixedSemantics_Singletons67`, `MutuallyUnbiased_MixedSemantics_Singletons68`, `MutuallyUnbiased_MixedSemantics_Singletons69`, `MutuallyUnbiased_MixedSemantics_Singletons70`, `MutuallyUnbiased_MixedSemantics_Singletons71`, `MutuallyUnbiased_MixedSemantics_Singletons72`, `MutuallyUnbiased_MixedSemantics_Singletons73`, `MutuallyUnbiased_MixedSemantics_Singletons74`, `MutuallyUnbiased_MixedSemantics_Singletons75`, `MutuallyUnbiased_MixedSemantics_Singletons76`, `MutuallyUnbiased_MixedSemantics_Singletons77`, `MutuallyUnbiased_MixedSemantics_Singletons78`, `MutuallyUnbiased_MixedSemantics_Singletons79`, `MutuallyUnbiased_MixedSemantics_Singletons80`, `MutuallyUnbiased_MixedSemantics_Singletons81`, `MutuallyUnbiased_MixedSemantics_Singletons82`, `MutuallyUnbiased_MixedSemantics_Singletons83`, `MutuallyUnbiased_MixedSemantics_Singletons84`, `MutuallyUnbiased_MixedSemantics_Singletons85`, `MutuallyUnbiased_PairSemantics_Boundary0`, `MutuallyUnbiased_PairSemantics_Boundary1`, `MutuallyUnbiased_PairSemantics_Boundary10`, `MutuallyUnbiased_PairSemantics_Boundary11`, `MutuallyUnbiased_PairSemantics_Boundary12`, `MutuallyUnbiased_PairSemantics_Boundary13`, `MutuallyUnbiased_PairSemantics_Boundary14`, `MutuallyUnbiased_PairSemantics_Boundary15`, `MutuallyUnbiased_PairSemantics_Boundary16`, `MutuallyUnbiased_PairSemantics_Boundary2`, `MutuallyUnbiased_PairSemantics_Boundary3`, `MutuallyUnbiased_PairSemantics_Boundary4`, `MutuallyUnbiased_PairSemantics_Boundary5`, `MutuallyUnbiased_PairSemantics_Boundary6`, `MutuallyUnbiased_PairSemantics_Boundary7`, `MutuallyUnbiased_PairSemantics_Boundary8`, `MutuallyUnbiased_PairSemantics_Boundary9`, `MutuallyUnbiased_PairSemantics_Nodes0`, `MutuallyUnbiased_PairSemantics_Nodes1`, `MutuallyUnbiased_PairSemantics_Nodes15`, `MutuallyUnbiased_PairSemantics_Nodes16`, `MutuallyUnbiased_PairSemantics_Nodes17`, `MutuallyUnbiased_PairSemantics_Nodes18`, `MutuallyUnbiased_PairSemantics_Nodes19`, `MutuallyUnbiased_PairSemantics_Nodes2`, `MutuallyUnbiased_PairSemantics_Nodes20`, `MutuallyUnbiased_PairSemantics_Nodes21`, `MutuallyUnbiased_PairSemantics_Nodes22`, `MutuallyUnbiased_PairSemantics_Nodes23`, `MutuallyUnbiased_PairSemantics_Nodes24`, `MutuallyUnbiased_PairSemantics_Nodes25`, `MutuallyUnbiased_PairSemantics_Nodes26`, `MutuallyUnbiased_PairSemantics_Nodes27`, `MutuallyUnbiased_PairSemantics_Nodes28`, `MutuallyUnbiased_PairSemantics_Nodes29`, `MutuallyUnbiased_PairSemantics_Nodes3`, `MutuallyUnbiased_PairSemantics_Nodes30`, `MutuallyUnbiased_PairSemantics_Nodes31`, `MutuallyUnbiased_PairSemantics_Nodes32`, `MutuallyUnbiased_PairSemantics_Nodes33`, `MutuallyUnbiased_PairSemantics_Nodes34`, `MutuallyUnbiased_PairSemantics_Nodes35`, `MutuallyUnbiased_PairSemantics_Nodes36`, `MutuallyUnbiased_PairSemantics_Nodes37`, `MutuallyUnbiased_PairSemantics_Nodes38`, `MutuallyUnbiased_PairSemantics_Nodes39`, `MutuallyUnbiased_PairSemantics_Nodes4`, `MutuallyUnbiased_PairSemantics_Nodes40`, `MutuallyUnbiased_PairSemantics_Nodes41`, `MutuallyUnbiased_PairSemantics_Nodes42`, `MutuallyUnbiased_PairSemantics_Nodes43`, `MutuallyUnbiased_PairSemantics_Nodes44`, `MutuallyUnbiased_PairSemantics_Nodes45`, `MutuallyUnbiased_PairSemantics_Nodes46`, `MutuallyUnbiased_PairSemantics_Nodes47`, `MutuallyUnbiased_PairSemantics_Nodes48`, `MutuallyUnbiased_PairSemantics_Nodes49`, `MutuallyUnbiased_PairSemantics_Nodes5`, `MutuallyUnbiased_PairSemantics_Nodes50`, `MutuallyUnbiased_PairSemantics_Nodes51`, `MutuallyUnbiased_PairSemantics_Nodes52`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e` and `OAI.MUB6.Certificate.PairSemantics.sound3364_e`; the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1162_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1170_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1340_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1341_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1342_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1343_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1395_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1396_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1397_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1399_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1409_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1410_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1411_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1412_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1414_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1441_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2357_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2358_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2526_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2527_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2528_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2530_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2531_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2570_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2572_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2574_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2576_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2599_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2636_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2901_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2903_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2904_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2939_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2941_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2943_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2957_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2958_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2959_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2960_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2961_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2963_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2986_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2987_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2988_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2996_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3081_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3082_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3087_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3088_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3089_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3139_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3140_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3184_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3185_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3190_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3191_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3203_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3204_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3205_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3206_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3209_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3210_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3211_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5167_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5168_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5169_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5174_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5292_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5386_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5388_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5416_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5417_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5433_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5434_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5435_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5476_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5482_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5483_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5485_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound136_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound142_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound145_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound146_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound147_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound148_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound149_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound150_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound47_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound52_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound67_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1472_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1436_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2168_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2169_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2171_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2172_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2173_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2174_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2175_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2180_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2181_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2182_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2183_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2185_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2187_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2189_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2192_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2193_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2196_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2198_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2200_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2201_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2202_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2203_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2204_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2205_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2206_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2208_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2211_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2212_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2215_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2216_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2217_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2218_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2219_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2220_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2223_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2224_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2225_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2227_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2228_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2229_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2230_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2235_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2238_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2240_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2241_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2242_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2246_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2247_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2248_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2249_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2250_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2251_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2252_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2253_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2254_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2256_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2257_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2258_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2259_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2260_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2263_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2265_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2270_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2271_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2273_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2274_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2275_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2276_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2277_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2283_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2284_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2285_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2288_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2289_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2290_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2291_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2293_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2295_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2297_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2298_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2302_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2304_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2305_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2306_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2307_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2308_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2313_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2314_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2315_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2316_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2317_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2322_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2323_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2325_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2328_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2329_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2330_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2331_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2332_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2333_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2334_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2336_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2337_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2338_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2346_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2347_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2348_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2350_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2352_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2361_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2362_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2363_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2364_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2373_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2374_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2375_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2376_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2377_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2378_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2379_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2381_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2382_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2383_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2384_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2385_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2386_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2387_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2390_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2393_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2394_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2397_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2398_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2399_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2400_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2401_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2402_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2405_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2406_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2407_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2408_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2415_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2416_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2422_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2424_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound720_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound882_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval285_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval287_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval289_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval296_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval301_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval308_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval310_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval316_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval325_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval332_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval335_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval338_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval339_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval341_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval343_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval351_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval352_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval356_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval357_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval358_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval359_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval366_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval369_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval372_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval378_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval37_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval382_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval383_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval385_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval390_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval398_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval39_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval405_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval408_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval46_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval476_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval53_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval55_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval56_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval63_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval69_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval73_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval74_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval79_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval373_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval375_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval44_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound26_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound49_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound58_e`, `OAI.MUB6.Certificate.PairSemantics.boundarySound73_e`, `OAI.MUB6.Certificate.PairSemantics.sound1379_e`, `OAI.MUB6.Certificate.PairSemantics.sound1381_e`, `OAI.MUB6.Certificate.PairSemantics.sound1383_e`, `OAI.MUB6.Certificate.PairSemantics.sound1384_e`, `OAI.MUB6.Certificate.PairSemantics.sound1387_e`, `OAI.MUB6.Certificate.PairSemantics.sound1390_e`, `OAI.MUB6.Certificate.PairSemantics.sound1391_e`, `OAI.MUB6.Certificate.PairSemantics.sound1395_e`, `OAI.MUB6.Certificate.PairSemantics.sound1399_e`, `OAI.MUB6.Certificate.PairSemantics.sound1414_e`, `OAI.MUB6.Certificate.PairSemantics.sound1419_e`, `OAI.MUB6.Certificate.PairSemantics.sound1423_e`, `OAI.MUB6.Certificate.PairSemantics.sound1424_e`, `OAI.MUB6.Certificate.PairSemantics.sound1425_e`, `OAI.MUB6.Certificate.PairSemantics.sound1434_e`, `OAI.MUB6.Certificate.PairSemantics.sound1437_e`, `OAI.MUB6.Certificate.PairSemantics.sound1443_e`, `OAI.MUB6.Certificate.PairSemantics.sound1458_e`, `OAI.MUB6.Certificate.PairSemantics.sound1486_e`, `OAI.MUB6.Certificate.PairSemantics.sound1504_e`, `OAI.MUB6.Certificate.PairSemantics.sound1506_e`, `OAI.MUB6.Certificate.PairSemantics.sound1512_e`, `OAI.MUB6.Certificate.PairSemantics.sound1518_e`, `OAI.MUB6.Certificate.PairSemantics.sound1529_e`, `OAI.MUB6.Certificate.PairSemantics.sound1530_e`, `OAI.MUB6.Certificate.PairSemantics.sound1531_e`, `OAI.MUB6.Certificate.PairSemantics.sound1535_e`, `OAI.MUB6.Certificate.PairSemantics.sound1540_e`, `OAI.MUB6.Certificate.PairSemantics.sound1548_e`, `OAI.MUB6.Certificate.PairSemantics.sound1605_e`, `OAI.MUB6.Certificate.PairSemantics.sound1614_e`, `OAI.MUB6.Certificate.PairSemantics.sound1617_e`, `OAI.MUB6.Certificate.PairSemantics.sound1624_e`, `OAI.MUB6.Certificate.PairSemantics.sound1627_e`, `OAI.MUB6.Certificate.PairSemantics.sound1628_e`, `OAI.MUB6.Certificate.PairSemantics.sound1631_e`, `OAI.MUB6.Certificate.PairSemantics.sound1634_e`, `OAI.MUB6.Certificate.PairSemantics.sound1635_e`, `OAI.MUB6.Certificate.PairSemantics.sound1637_e`, `OAI.MUB6.Certificate.PairSemantics.sound1644_e`, `OAI.MUB6.Certificate.PairSemantics.sound1646_e`, `OAI.MUB6.Certificate.PairSemantics.sound1648_e`, `OAI.MUB6.Certificate.PairSemantics.sound1685_e`, `OAI.MUB6.Certificate.PairSemantics.sound1716_e`, `OAI.MUB6.Certificate.PairSemantics.sound1736_e`, `OAI.MUB6.Certificate.PairSemantics.sound1739_e`, `OAI.MUB6.Certificate.PairSemantics.sound1768_e`, `OAI.MUB6.Certificate.PairSemantics.sound1770_e`, `OAI.MUB6.Certificate.PairSemantics.sound1793_e`, `OAI.MUB6.Certificate.PairSemantics.sound1800_e`, `OAI.MUB6.Certificate.PairSemantics.sound1828_e`, `OAI.MUB6.Certificate.PairSemantics.sound1849_e`, `OAI.MUB6.Certificate.PairSemantics.sound1858_e`, `OAI.MUB6.Certificate.PairSemantics.sound1860_e`, `OAI.MUB6.Certificate.PairSemantics.sound1865_e`, `OAI.MUB6.Certificate.PairSemantics.sound1866_e`, `OAI.MUB6.Certificate.PairSemantics.sound1867_e`, `OAI.MUB6.Certificate.PairSemantics.sound1869_e`, `OAI.MUB6.Certificate.PairSemantics.sound1870_e`, `OAI.MUB6.Certificate.PairSemantics.sound1872_e`, `OAI.MUB6.Certificate.PairSemantics.sound1875_e`, `OAI.MUB6.Certificate.PairSemantics.sound1876_e`, `OAI.MUB6.Certificate.PairSemantics.sound1879_e`, `OAI.MUB6.Certificate.PairSemantics.sound1885_e`, `OAI.MUB6.Certificate.PairSemantics.sound1978_e`, `OAI.MUB6.Certificate.PairSemantics.sound1980_e`, `OAI.MUB6.Certificate.PairSemantics.sound1986_e`, `OAI.MUB6.Certificate.PairSemantics.sound1987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2041_e`, `OAI.MUB6.Certificate.PairSemantics.sound2058_e`, `OAI.MUB6.Certificate.PairSemantics.sound2071_e`, `OAI.MUB6.Certificate.PairSemantics.sound2097_e`, `OAI.MUB6.Certificate.PairSemantics.sound2106_e`, `OAI.MUB6.Certificate.PairSemantics.sound2107_e`, `OAI.MUB6.Certificate.PairSemantics.sound2108_e`, `OAI.MUB6.Certificate.PairSemantics.sound2117_e`, `OAI.MUB6.Certificate.PairSemantics.sound2122_e`, `OAI.MUB6.Certificate.PairSemantics.sound2123_e`, `OAI.MUB6.Certificate.PairSemantics.sound2128_e`, `OAI.MUB6.Certificate.PairSemantics.sound2132_e`, `OAI.MUB6.Certificate.PairSemantics.sound2152_e`, `OAI.MUB6.Certificate.PairSemantics.sound2168_e`, `OAI.MUB6.Certificate.PairSemantics.sound2175_e`, `OAI.MUB6.Certificate.PairSemantics.sound2177_e`, `OAI.MUB6.Certificate.PairSemantics.sound2189_e`, `OAI.MUB6.Certificate.PairSemantics.sound2190_e`, `OAI.MUB6.Certificate.PairSemantics.sound2197_e`, `OAI.MUB6.Certificate.PairSemantics.sound2201_e`, `OAI.MUB6.Certificate.PairSemantics.sound2202_e`, `OAI.MUB6.Certificate.PairSemantics.sound2213_e`, `OAI.MUB6.Certificate.PairSemantics.sound2228_e`, `OAI.MUB6.Certificate.PairSemantics.sound2244_e`, `OAI.MUB6.Certificate.PairSemantics.sound2262_e`, `OAI.MUB6.Certificate.PairSemantics.sound2284_e`, `OAI.MUB6.Certificate.PairSemantics.sound2286_e`, `OAI.MUB6.Certificate.PairSemantics.sound2293_e`, `OAI.MUB6.Certificate.PairSemantics.sound2294_e`, `OAI.MUB6.Certificate.PairSemantics.sound2295_e`, `OAI.MUB6.Certificate.PairSemantics.sound2296_e`, `OAI.MUB6.Certificate.PairSemantics.sound2312_e`, `OAI.MUB6.Certificate.PairSemantics.sound2324_e`, `OAI.MUB6.Certificate.PairSemantics.sound2327_e`, `OAI.MUB6.Certificate.PairSemantics.sound2338_e`, `OAI.MUB6.Certificate.PairSemantics.sound2375_e`, `OAI.MUB6.Certificate.PairSemantics.sound2382_e`, `OAI.MUB6.Certificate.PairSemantics.sound2390_e`, `OAI.MUB6.Certificate.PairSemantics.sound2391_e`, `OAI.MUB6.Certificate.PairSemantics.sound2394_e`, `OAI.MUB6.Certificate.PairSemantics.sound2399_e`, `OAI.MUB6.Certificate.PairSemantics.sound2400_e`, `OAI.MUB6.Certificate.PairSemantics.sound2401_e`, `OAI.MUB6.Certificate.PairSemantics.sound2403_e`, `OAI.MUB6.Certificate.PairSemantics.sound2415_e`, `OAI.MUB6.Certificate.PairSemantics.sound2416_e`, `OAI.MUB6.Certificate.PairSemantics.sound2420_e`, `OAI.MUB6.Certificate.PairSemantics.sound2433_e`, `OAI.MUB6.Certificate.PairSemantics.sound2434_e`, `OAI.MUB6.Certificate.PairSemantics.sound2435_e`, `OAI.MUB6.Certificate.PairSemantics.sound2436_e`, `OAI.MUB6.Certificate.PairSemantics.sound2442_e`, `OAI.MUB6.Certificate.PairSemantics.sound2444_e`, `OAI.MUB6.Certificate.PairSemantics.sound2445_e`, `OAI.MUB6.Certificate.PairSemantics.sound2454_e`, `OAI.MUB6.Certificate.PairSemantics.sound2456_e`, `OAI.MUB6.Certificate.PairSemantics.sound2457_e`, `OAI.MUB6.Certificate.PairSemantics.sound2463_e`, `OAI.MUB6.Certificate.PairSemantics.sound2464_e`, `OAI.MUB6.Certificate.PairSemantics.sound2465_e`, `OAI.MUB6.Certificate.PairSemantics.sound2472_e`, `OAI.MUB6.Certificate.PairSemantics.sound2473_e`, `OAI.MUB6.Certificate.PairSemantics.sound2477_e`, `OAI.MUB6.Certificate.PairSemantics.sound2479_e`, `OAI.MUB6.Certificate.PairSemantics.sound2489_e`, `OAI.MUB6.Certificate.PairSemantics.sound2490_e`, `OAI.MUB6.Certificate.PairSemantics.sound2491_e`, `OAI.MUB6.Certificate.PairSemantics.sound2492_e`, `OAI.MUB6.Certificate.PairSemantics.sound2507_e`, `OAI.MUB6.Certificate.PairSemantics.sound2520_e`, `OAI.MUB6.Certificate.PairSemantics.sound2521_e`, `OAI.MUB6.Certificate.PairSemantics.sound2522_e`, `OAI.MUB6.Certificate.PairSemantics.sound2524_e`, `OAI.MUB6.Certificate.PairSemantics.sound2525_e`, `OAI.MUB6.Certificate.PairSemantics.sound2527_e`, `OAI.MUB6.Certificate.PairSemantics.sound2533_e`, `OAI.MUB6.Certificate.PairSemantics.sound2540_e`, `OAI.MUB6.Certificate.PairSemantics.sound2546_e`, `OAI.MUB6.Certificate.PairSemantics.sound2547_e`, `OAI.MUB6.Certificate.PairSemantics.sound2548_e`, `OAI.MUB6.Certificate.PairSemantics.sound2557_e`, `OAI.MUB6.Certificate.PairSemantics.sound2558_e`, `OAI.MUB6.Certificate.PairSemantics.sound2559_e`, `OAI.MUB6.Certificate.PairSemantics.sound2564_e`, `OAI.MUB6.Certificate.PairSemantics.sound2565_e`, `OAI.MUB6.Certificate.PairSemantics.sound2566_e`, `OAI.MUB6.Certificate.PairSemantics.sound2573_e`, `OAI.MUB6.Certificate.PairSemantics.sound2578_e`, `OAI.MUB6.Certificate.PairSemantics.sound2580_e`, `OAI.MUB6.Certificate.PairSemantics.sound2593_e`, `OAI.MUB6.Certificate.PairSemantics.sound2602_e`, `OAI.MUB6.Certificate.PairSemantics.sound2604_e`, `OAI.MUB6.Certificate.PairSemantics.sound2606_e`, `OAI.MUB6.Certificate.PairSemantics.sound2619_e`, `OAI.MUB6.Certificate.PairSemantics.sound2620_e`, `OAI.MUB6.Certificate.PairSemantics.sound2623_e`, `OAI.MUB6.Certificate.PairSemantics.sound2627_e`, `OAI.MUB6.Certificate.PairSemantics.sound2641_e`, `OAI.MUB6.Certificate.PairSemantics.sound2657_e`, `OAI.MUB6.Certificate.PairSemantics.sound2658_e`, `OAI.MUB6.Certificate.PairSemantics.sound2661_e`, `OAI.MUB6.Certificate.PairSemantics.sound2666_e`, `OAI.MUB6.Certificate.PairSemantics.sound2669_e`, `OAI.MUB6.Certificate.PairSemantics.sound2670_e`, `OAI.MUB6.Certificate.PairSemantics.sound2671_e`, `OAI.MUB6.Certificate.PairSemantics.sound2686_e`, `OAI.MUB6.Certificate.PairSemantics.sound2690_e`, `OAI.MUB6.Certificate.PairSemantics.sound2693_e`, `OAI.MUB6.Certificate.PairSemantics.sound2698_e`, `OAI.MUB6.Certificate.PairSemantics.sound2708_e`, `OAI.MUB6.Certificate.PairSemantics.sound2710_e`, `OAI.MUB6.Certificate.PairSemantics.sound2714_e`, `OAI.MUB6.Certificate.PairSemantics.sound2729_e`, `OAI.MUB6.Certificate.PairSemantics.sound2732_e`, `OAI.MUB6.Certificate.PairSemantics.sound2733_e`, `OAI.MUB6.Certificate.PairSemantics.sound2735_e`, `OAI.MUB6.Certificate.PairSemantics.sound2754_e`, `OAI.MUB6.Certificate.PairSemantics.sound2757_e`, `OAI.MUB6.Certificate.PairSemantics.sound2788_e`, `OAI.MUB6.Certificate.PairSemantics.sound2790_e`, `OAI.MUB6.Certificate.PairSemantics.sound2793_e`, `OAI.MUB6.Certificate.PairSemantics.sound2807_e`, `OAI.MUB6.Certificate.PairSemantics.sound2817_e`, `OAI.MUB6.Certificate.PairSemantics.sound2829_e`, `OAI.MUB6.Certificate.PairSemantics.sound2836_e`, `OAI.MUB6.Certificate.PairSemantics.sound2845_e`, `OAI.MUB6.Certificate.PairSemantics.sound2853_e`, `OAI.MUB6.Certificate.PairSemantics.sound2854_e`, `OAI.MUB6.Certificate.PairSemantics.sound2858_e`, `OAI.MUB6.Certificate.PairSemantics.sound2863_e`, `OAI.MUB6.Certificate.PairSemantics.sound2864_e`, `OAI.MUB6.Certificate.PairSemantics.sound2865_e`, `OAI.MUB6.Certificate.PairSemantics.sound2866_e`, `OAI.MUB6.Certificate.PairSemantics.sound2867_e`, `OAI.MUB6.Certificate.PairSemantics.sound2868_e`, `OAI.MUB6.Certificate.PairSemantics.sound2872_e`, `OAI.MUB6.Certificate.PairSemantics.sound2873_e`, `OAI.MUB6.Certificate.PairSemantics.sound2874_e`, `OAI.MUB6.Certificate.PairSemantics.sound2875_e`, `OAI.MUB6.Certificate.PairSemantics.sound2878_e`, `OAI.MUB6.Certificate.PairSemantics.sound2879_e`, `OAI.MUB6.Certificate.PairSemantics.sound2880_e`, `OAI.MUB6.Certificate.PairSemantics.sound2882_e`, `OAI.MUB6.Certificate.PairSemantics.sound2883_e`, `OAI.MUB6.Certificate.PairSemantics.sound2884_e`, `OAI.MUB6.Certificate.PairSemantics.sound2887_e`, `OAI.MUB6.Certificate.PairSemantics.sound2888_e`, `OAI.MUB6.Certificate.PairSemantics.sound2889_e`, `OAI.MUB6.Certificate.PairSemantics.sound2890_e`, `OAI.MUB6.Certificate.PairSemantics.sound2891_e`, `OAI.MUB6.Certificate.PairSemantics.sound2892_e`, `OAI.MUB6.Certificate.PairSemantics.sound2894_e`, `OAI.MUB6.Certificate.PairSemantics.sound2895_e`, `OAI.MUB6.Certificate.PairSemantics.sound2896_e`, `OAI.MUB6.Certificate.PairSemantics.sound2897_e`, `OAI.MUB6.Certificate.PairSemantics.sound2898_e`, `OAI.MUB6.Certificate.PairSemantics.sound2899_e`, `OAI.MUB6.Certificate.PairSemantics.sound2900_e`, `OAI.MUB6.Certificate.PairSemantics.sound2901_e`, `OAI.MUB6.Certificate.PairSemantics.sound2902_e`, `OAI.MUB6.Certificate.PairSemantics.sound2904_e`, `OAI.MUB6.Certificate.PairSemantics.sound2905_e`, `OAI.MUB6.Certificate.PairSemantics.sound2906_e`, `OAI.MUB6.Certificate.PairSemantics.sound2908_e`, `OAI.MUB6.Certificate.PairSemantics.sound2909_e`, `OAI.MUB6.Certificate.PairSemantics.sound2910_e`, `OAI.MUB6.Certificate.PairSemantics.sound2912_e`, `OAI.MUB6.Certificate.PairSemantics.sound2913_e`, `OAI.MUB6.Certificate.PairSemantics.sound2914_e`, `OAI.MUB6.Certificate.PairSemantics.sound2915_e`, `OAI.MUB6.Certificate.PairSemantics.sound2916_e`, `OAI.MUB6.Certificate.PairSemantics.sound2917_e`, `OAI.MUB6.Certificate.PairSemantics.sound2919_e`, `OAI.MUB6.Certificate.PairSemantics.sound2920_e`, `OAI.MUB6.Certificate.PairSemantics.sound2922_e`, `OAI.MUB6.Certificate.PairSemantics.sound2924_e`, `OAI.MUB6.Certificate.PairSemantics.sound2925_e`, `OAI.MUB6.Certificate.PairSemantics.sound2926_e`, `OAI.MUB6.Certificate.PairSemantics.sound2927_e`, `OAI.MUB6.Certificate.PairSemantics.sound2928_e`, `OAI.MUB6.Certificate.PairSemantics.sound2929_e`, `OAI.MUB6.Certificate.PairSemantics.sound2931_e`, `OAI.MUB6.Certificate.PairSemantics.sound2933_e`, `OAI.MUB6.Certificate.PairSemantics.sound2935_e`, `OAI.MUB6.Certificate.PairSemantics.sound2936_e`, `OAI.MUB6.Certificate.PairSemantics.sound2939_e`, `OAI.MUB6.Certificate.PairSemantics.sound2940_e`, `OAI.MUB6.Certificate.PairSemantics.sound2941_e`, `OAI.MUB6.Certificate.PairSemantics.sound2942_e`, `OAI.MUB6.Certificate.PairSemantics.sound2943_e`, `OAI.MUB6.Certificate.PairSemantics.sound2944_e`, `OAI.MUB6.Certificate.PairSemantics.sound2946_e`, `OAI.MUB6.Certificate.PairSemantics.sound2949_e`, `OAI.MUB6.Certificate.PairSemantics.sound2950_e`, `OAI.MUB6.Certificate.PairSemantics.sound2951_e`, `OAI.MUB6.Certificate.PairSemantics.sound2952_e`, `OAI.MUB6.Certificate.PairSemantics.sound2953_e`, `OAI.MUB6.Certificate.PairSemantics.sound2954_e`, `OAI.MUB6.Certificate.PairSemantics.sound2956_e`, `OAI.MUB6.Certificate.PairSemantics.sound2957_e`, `OAI.MUB6.Certificate.PairSemantics.sound2959_e`, `OAI.MUB6.Certificate.PairSemantics.sound2960_e`, `OAI.MUB6.Certificate.PairSemantics.sound2961_e`, `OAI.MUB6.Certificate.PairSemantics.sound2962_e`, `OAI.MUB6.Certificate.PairSemantics.sound2963_e`, `OAI.MUB6.Certificate.PairSemantics.sound2964_e`, `OAI.MUB6.Certificate.PairSemantics.sound2965_e`, `OAI.MUB6.Certificate.PairSemantics.sound2966_e`, `OAI.MUB6.Certificate.PairSemantics.sound2967_e`, `OAI.MUB6.Certificate.PairSemantics.sound2968_e`, `OAI.MUB6.Certificate.PairSemantics.sound2969_e`, `OAI.MUB6.Certificate.PairSemantics.sound2970_e`, `OAI.MUB6.Certificate.PairSemantics.sound2972_e`, `OAI.MUB6.Certificate.PairSemantics.sound2973_e`, `OAI.MUB6.Certificate.PairSemantics.sound2974_e`, `OAI.MUB6.Certificate.PairSemantics.sound2975_e`, `OAI.MUB6.Certificate.PairSemantics.sound2976_e`, `OAI.MUB6.Certificate.PairSemantics.sound2977_e`, `OAI.MUB6.Certificate.PairSemantics.sound2979_e`, `OAI.MUB6.Certificate.PairSemantics.sound2980_e`, `OAI.MUB6.Certificate.PairSemantics.sound2984_e`, `OAI.MUB6.Certificate.PairSemantics.sound2985_e`, `OAI.MUB6.Certificate.PairSemantics.sound2986_e`, `OAI.MUB6.Certificate.PairSemantics.sound2987_e`, `OAI.MUB6.Certificate.PairSemantics.sound2989_e`, `OAI.MUB6.Certificate.PairSemantics.sound2990_e`, `OAI.MUB6.Certificate.PairSemantics.sound2991_e`, `OAI.MUB6.Certificate.PairSemantics.sound2992_e`, `OAI.MUB6.Certificate.PairSemantics.sound2994_e`, `OAI.MUB6.Certificate.PairSemantics.sound2996_e`, `OAI.MUB6.Certificate.PairSemantics.sound2997_e`, `OAI.MUB6.Certificate.PairSemantics.sound2998_e`, `OAI.MUB6.Certificate.PairSemantics.sound2999_e`, `OAI.MUB6.Certificate.PairSemantics.sound3000_e`, `OAI.MUB6.Certificate.PairSemantics.sound3001_e`, `OAI.MUB6.Certificate.PairSemantics.sound3002_e`, `OAI.MUB6.Certificate.PairSemantics.sound3004_e`, `OAI.MUB6.Certificate.PairSemantics.sound3006_e`, `OAI.MUB6.Certificate.PairSemantics.sound3007_e`, `OAI.MUB6.Certificate.PairSemantics.sound3009_e`, `OAI.MUB6.Certificate.PairSemantics.sound3011_e`, `OAI.MUB6.Certificate.PairSemantics.sound3012_e`, `OAI.MUB6.Certificate.PairSemantics.sound3013_e`, `OAI.MUB6.Certificate.PairSemantics.sound3014_e`, `OAI.MUB6.Certificate.PairSemantics.sound3015_e`, `OAI.MUB6.Certificate.PairSemantics.sound3016_e`, `OAI.MUB6.Certificate.PairSemantics.sound3017_e`, `OAI.MUB6.Certificate.PairSemantics.sound3018_e`, `OAI.MUB6.Certificate.PairSemantics.sound3019_e`, `OAI.MUB6.Certificate.PairSemantics.sound3020_e`, `OAI.MUB6.Certificate.PairSemantics.sound3021_e`, `OAI.MUB6.Certificate.PairSemantics.sound3022_e`, `OAI.MUB6.Certificate.PairSemantics.sound3023_e`, `OAI.MUB6.Certificate.PairSemantics.sound3024_e`, `OAI.MUB6.Certificate.PairSemantics.sound3025_e`, `OAI.MUB6.Certificate.PairSemantics.sound3026_e`, `OAI.MUB6.Certificate.PairSemantics.sound3027_e`, `OAI.MUB6.Certificate.PairSemantics.sound3028_e`, `OAI.MUB6.Certificate.PairSemantics.sound3029_e`, `OAI.MUB6.Certificate.PairSemantics.sound3030_e`, `OAI.MUB6.Certificate.PairSemantics.sound3032_e`, `OAI.MUB6.Certificate.PairSemantics.sound3034_e`, `OAI.MUB6.Certificate.PairSemantics.sound3035_e`, `OAI.MUB6.Certificate.PairSemantics.sound3036_e`, `OAI.MUB6.Certificate.PairSemantics.sound3037_e`, `OAI.MUB6.Certificate.PairSemantics.sound3038_e`, `OAI.MUB6.Certificate.PairSemantics.sound3039_e`, `OAI.MUB6.Certificate.PairSemantics.sound3040_e`, `OAI.MUB6.Certificate.PairSemantics.sound3041_e`, `OAI.MUB6.Certificate.PairSemantics.sound3042_e`, `OAI.MUB6.Certificate.PairSemantics.sound3045_e`, `OAI.MUB6.Certificate.PairSemantics.sound3049_e`, `OAI.MUB6.Certificate.PairSemantics.sound3050_e`, `OAI.MUB6.Certificate.PairSemantics.sound3051_e`, `OAI.MUB6.Certificate.PairSemantics.sound3052_e`, `OAI.MUB6.Certificate.PairSemantics.sound3053_e`, `OAI.MUB6.Certificate.PairSemantics.sound3054_e`, `OAI.MUB6.Certificate.PairSemantics.sound3055_e`, `OAI.MUB6.Certificate.PairSemantics.sound3057_e`, `OAI.MUB6.Certificate.PairSemantics.sound3059_e`, `OAI.MUB6.Certificate.PairSemantics.sound3060_e`, `OAI.MUB6.Certificate.PairSemantics.sound3061_e`, `OAI.MUB6.Certificate.PairSemantics.sound3062_e`, `OAI.MUB6.Certificate.PairSemantics.sound3063_e`, `OAI.MUB6.Certificate.PairSemantics.sound3065_e`, `OAI.MUB6.Certificate.PairSemantics.sound3066_e`, `OAI.MUB6.Certificate.PairSemantics.sound3067_e`, `OAI.MUB6.Certificate.PairSemantics.sound3068_e`, `OAI.MUB6.Certificate.PairSemantics.sound3069_e`, `OAI.MUB6.Certificate.PairSemantics.sound3071_e`, `OAI.MUB6.Certificate.PairSemantics.sound3072_e`, `OAI.MUB6.Certificate.PairSemantics.sound3073_e`, `OAI.MUB6.Certificate.PairSemantics.sound3074_e`, `OAI.MUB6.Certificate.PairSemantics.sound3075_e`, `OAI.MUB6.Certificate.PairSemantics.sound3076_e`, `OAI.MUB6.Certificate.PairSemantics.sound3077_e`, `OAI.MUB6.Certificate.PairSemantics.sound3078_e`, `OAI.MUB6.Certificate.PairSemantics.sound3079_e`, `OAI.MUB6.Certificate.PairSemantics.sound3081_e`, `OAI.MUB6.Certificate.PairSemantics.sound3082_e`, `OAI.MUB6.Certificate.PairSemantics.sound3084_e`, `OAI.MUB6.Certificate.PairSemantics.sound3085_e`, `OAI.MUB6.Certificate.PairSemantics.sound3086_e`, `OAI.MUB6.Certificate.PairSemantics.sound3087_e`, `OAI.MUB6.Certificate.PairSemantics.sound3088_e`, `OAI.MUB6.Certificate.PairSemantics.sound3090_e`, `OAI.MUB6.Certificate.PairSemantics.sound3091_e`, `OAI.MUB6.Certificate.PairSemantics.sound3092_e`, `OAI.MUB6.Certificate.PairSemantics.sound3093_e`, `OAI.MUB6.Certificate.PairSemantics.sound3094_e`, `OAI.MUB6.Certificate.PairSemantics.sound3095_e`, `OAI.MUB6.Certificate.PairSemantics.sound3096_e`, `OAI.MUB6.Certificate.PairSemantics.sound3098_e`, `OAI.MUB6.Certificate.PairSemantics.sound3099_e`, `OAI.MUB6.Certificate.PairSemantics.sound3100_e`, `OAI.MUB6.Certificate.PairSemantics.sound3101_e`, `OAI.MUB6.Certificate.PairSemantics.sound3105_e`, `OAI.MUB6.Certificate.PairSemantics.sound3106_e`, `OAI.MUB6.Certificate.PairSemantics.sound3107_e`, `OAI.MUB6.Certificate.PairSemantics.sound3108_e`, `OAI.MUB6.Certificate.PairSemantics.sound3110_e`, `OAI.MUB6.Certificate.PairSemantics.sound3111_e`, `OAI.MUB6.Certificate.PairSemantics.sound3112_e`, `OAI.MUB6.Certificate.PairSemantics.sound3113_e`, `OAI.MUB6.Certificate.PairSemantics.sound3114_e`, `OAI.MUB6.Certificate.PairSemantics.sound3115_e`, `OAI.MUB6.Certificate.PairSemantics.sound3118_e`, `OAI.MUB6.Certificate.PairSemantics.sound3119_e`, `OAI.MUB6.Certificate.PairSemantics.sound3120_e`, `OAI.MUB6.Certificate.PairSemantics.sound3122_e`, `OAI.MUB6.Certificate.PairSemantics.sound3123_e`, `OAI.MUB6.Certificate.PairSemantics.sound3124_e`, `OAI.MUB6.Certificate.PairSemantics.sound3125_e`, `OAI.MUB6.Certificate.PairSemantics.sound3127_e`, `OAI.MUB6.Certificate.PairSemantics.sound3128_e`, `OAI.MUB6.Certificate.PairSemantics.sound3129_e`, `OAI.MUB6.Certificate.PairSemantics.sound3130_e`, `OAI.MUB6.Certificate.PairSemantics.sound3131_e`, `OAI.MUB6.Certificate.PairSemantics.sound3132_e`, `OAI.MUB6.Certificate.PairSemantics.sound3133_e`, `OAI.MUB6.Certificate.PairSemantics.sound3135_e`, `OAI.MUB6.Certificate.PairSemantics.sound3136_e`, `OAI.MUB6.Certificate.PairSemantics.sound3137_e`, `OAI.MUB6.Certificate.PairSemantics.sound3138_e`, `OAI.MUB6.Certificate.PairSemantics.sound3139_e`, `OAI.MUB6.Certificate.PairSemantics.sound3140_e`, `OAI.MUB6.Certificate.PairSemantics.sound3141_e`, `OAI.MUB6.Certificate.PairSemantics.sound3142_e`, `OAI.MUB6.Certificate.PairSemantics.sound3144_e`, `OAI.MUB6.Certificate.PairSemantics.sound3145_e`, `OAI.MUB6.Certificate.PairSemantics.sound3146_e`, `OAI.MUB6.Certificate.PairSemantics.sound3149_e`, `OAI.MUB6.Certificate.PairSemantics.sound3150_e`, `OAI.MUB6.Certificate.PairSemantics.sound3151_e`, `OAI.MUB6.Certificate.PairSemantics.sound3152_e`, `OAI.MUB6.Certificate.PairSemantics.sound3153_e`, `OAI.MUB6.Certificate.PairSemantics.sound3154_e`, `OAI.MUB6.Certificate.PairSemantics.sound3158_e`, `OAI.MUB6.Certificate.PairSemantics.sound3159_e`, `OAI.MUB6.Certificate.PairSemantics.sound3160_e`, `OAI.MUB6.Certificate.PairSemantics.sound3161_e`, `OAI.MUB6.Certificate.PairSemantics.sound3163_e`, `OAI.MUB6.Certificate.PairSemantics.sound3164_e`, `OAI.MUB6.Certificate.PairSemantics.sound3166_e`, `OAI.MUB6.Certificate.PairSemantics.sound3167_e`, `OAI.MUB6.Certificate.PairSemantics.sound3169_e`, `OAI.MUB6.Certificate.PairSemantics.sound3170_e`, `OAI.MUB6.Certificate.PairSemantics.sound3171_e`, `OAI.MUB6.Certificate.PairSemantics.sound3172_e`, `OAI.MUB6.Certificate.PairSemantics.sound3173_e`, `OAI.MUB6.Certificate.PairSemantics.sound3174_e`, `OAI.MUB6.Certificate.PairSemantics.sound3176_e`, `OAI.MUB6.Certificate.PairSemantics.sound3178_e`, `OAI.MUB6.Certificate.PairSemantics.sound3179_e`, `OAI.MUB6.Certificate.PairSemantics.sound3180_e`, `OAI.MUB6.Certificate.PairSemantics.sound3181_e`, `OAI.MUB6.Certificate.PairSemantics.sound3183_e`, `OAI.MUB6.Certificate.PairSemantics.sound3184_e`, `OAI.MUB6.Certificate.PairSemantics.sound3185_e`, `OAI.MUB6.Certificate.PairSemantics.sound3187_e`, `OAI.MUB6.Certificate.PairSemantics.sound3188_e`, `OAI.MUB6.Certificate.PairSemantics.sound3189_e`, `OAI.MUB6.Certificate.PairSemantics.sound3191_e`, `OAI.MUB6.Certificate.PairSemantics.sound3192_e`, `OAI.MUB6.Certificate.PairSemantics.sound3193_e`, `OAI.MUB6.Certificate.PairSemantics.sound3194_e`, `OAI.MUB6.Certificate.PairSemantics.sound3195_e`, `OAI.MUB6.Certificate.PairSemantics.sound3196_e`, `OAI.MUB6.Certificate.PairSemantics.sound3197_e`, `OAI.MUB6.Certificate.PairSemantics.sound3198_e`, `OAI.MUB6.Certificate.PairSemantics.sound3199_e`, `OAI.MUB6.Certificate.PairSemantics.sound3200_e`, `OAI.MUB6.Certificate.PairSemantics.sound3201_e`, `OAI.MUB6.Certificate.PairSemantics.sound3202_e`, `OAI.MUB6.Certificate.PairSemantics.sound3203_e`, `OAI.MUB6.Certificate.PairSemantics.sound3204_e`, `OAI.MUB6.Certificate.PairSemantics.sound3205_e`, `OAI.MUB6.Certificate.PairSemantics.sound3206_e`, `OAI.MUB6.Certificate.PairSemantics.sound3208_e`, `OAI.MUB6.Certificate.PairSemantics.sound3209_e`, `OAI.MUB6.Certificate.PairSemantics.sound3211_e`, `OAI.MUB6.Certificate.PairSemantics.sound3212_e`, `OAI.MUB6.Certificate.PairSemantics.sound3213_e`, `OAI.MUB6.Certificate.PairSemantics.sound3215_e`, `OAI.MUB6.Certificate.PairSemantics.sound3216_e`, `OAI.MUB6.Certificate.PairSemantics.sound3218_e`, `OAI.MUB6.Certificate.PairSemantics.sound3220_e`, `OAI.MUB6.Certificate.PairSemantics.sound3221_e`, `OAI.MUB6.Certificate.PairSemantics.sound3222_e`, `OAI.MUB6.Certificate.PairSemantics.sound3223_e`, `OAI.MUB6.Certificate.PairSemantics.sound3224_e`, `OAI.MUB6.Certificate.PairSemantics.sound3225_e`, `OAI.MUB6.Certificate.PairSemantics.sound3226_e`, `OAI.MUB6.Certificate.PairSemantics.sound3227_e`, `OAI.MUB6.Certificate.PairSemantics.sound3228_e`, `OAI.MUB6.Certificate.PairSemantics.sound3229_e`, `OAI.MUB6.Certificate.PairSemantics.sound3230_e`, `OAI.MUB6.Certificate.PairSemantics.sound3233_e`, `OAI.MUB6.Certificate.PairSemantics.sound3234_e`, `OAI.MUB6.Certificate.PairSemantics.sound3235_e`, `OAI.MUB6.Certificate.PairSemantics.sound3237_e`, `OAI.MUB6.Certificate.PairSemantics.sound3238_e`, `OAI.MUB6.Certificate.PairSemantics.sound3240_e`, `OAI.MUB6.Certificate.PairSemantics.sound3242_e`, `OAI.MUB6.Certificate.PairSemantics.sound3243_e`, `OAI.MUB6.Certificate.PairSemantics.sound3244_e`, `OAI.MUB6.Certificate.PairSemantics.sound3246_e`, `OAI.MUB6.Certificate.PairSemantics.sound3247_e`, `OAI.MUB6.Certificate.PairSemantics.sound3248_e`, `OAI.MUB6.Certificate.PairSemantics.sound3249_e`, `OAI.MUB6.Certificate.PairSemantics.sound3253_e`, `OAI.MUB6.Certificate.PairSemantics.sound3254_e`, `OAI.MUB6.Certificate.PairSemantics.sound3255_e`, `OAI.MUB6.Certificate.PairSemantics.sound3256_e`, `OAI.MUB6.Certificate.PairSemantics.sound3258_e`, `OAI.MUB6.Certificate.PairSemantics.sound3260_e`, `OAI.MUB6.Certificate.PairSemantics.sound3262_e`, `OAI.MUB6.Certificate.PairSemantics.sound3263_e`, `OAI.MUB6.Certificate.PairSemantics.sound3264_e`, `OAI.MUB6.Certificate.PairSemantics.sound3266_e`, `OAI.MUB6.Certificate.PairSemantics.sound3267_e`, `OAI.MUB6.Certificate.PairSemantics.sound3268_e`, `OAI.MUB6.Certificate.PairSemantics.sound3269_e`, `OAI.MUB6.Certificate.PairSemantics.sound3271_e`, `OAI.MUB6.Certificate.PairSemantics.sound3272_e`, `OAI.MUB6.Certificate.PairSemantics.sound3273_e`, `OAI.MUB6.Certificate.PairSemantics.sound3274_e`, `OAI.MUB6.Certificate.PairSemantics.sound3275_e`, `OAI.MUB6.Certificate.PairSemantics.sound3276_e`, `OAI.MUB6.Certificate.PairSemantics.sound3277_e`, `OAI.MUB6.Certificate.PairSemantics.sound3278_e`, `OAI.MUB6.Certificate.PairSemantics.sound3279_e`, `OAI.MUB6.Certificate.PairSemantics.sound3280_e`, `OAI.MUB6.Certificate.PairSemantics.sound3281_e`, `OAI.MUB6.Certificate.PairSemantics.sound3282_e`, `OAI.MUB6.Certificate.PairSemantics.sound3283_e`, `OAI.MUB6.Certificate.PairSemantics.sound3284_e`, `OAI.MUB6.Certificate.PairSemantics.sound3288_e`, `OAI.MUB6.Certificate.PairSemantics.sound3289_e`, `OAI.MUB6.Certificate.PairSemantics.sound3290_e`, `OAI.MUB6.Certificate.PairSemantics.sound3291_e`, `OAI.MUB6.Certificate.PairSemantics.sound3292_e`, `OAI.MUB6.Certificate.PairSemantics.sound3293_e`, `OAI.MUB6.Certificate.PairSemantics.sound3294_e`, `OAI.MUB6.Certificate.PairSemantics.sound3295_e`, `OAI.MUB6.Certificate.PairSemantics.sound3296_e`, `OAI.MUB6.Certificate.PairSemantics.sound3297_e`, `OAI.MUB6.Certificate.PairSemantics.sound3298_e`, `OAI.MUB6.Certificate.PairSemantics.sound3299_e`, `OAI.MUB6.Certificate.PairSemantics.sound3300_e`, `OAI.MUB6.Certificate.PairSemantics.sound3301_e`, `OAI.MUB6.Certificate.PairSemantics.sound3302_e`, `OAI.MUB6.Certificate.PairSemantics.sound3303_e`, `OAI.MUB6.Certificate.PairSemantics.sound3304_e`, `OAI.MUB6.Certificate.PairSemantics.sound3305_e`, `OAI.MUB6.Certificate.PairSemantics.sound3307_e`, `OAI.MUB6.Certificate.PairSemantics.sound3308_e`, `OAI.MUB6.Certificate.PairSemantics.sound3309_e`, `OAI.MUB6.Certificate.PairSemantics.sound3310_e`, `OAI.MUB6.Certificate.PairSemantics.sound3311_e`, `OAI.MUB6.Certificate.PairSemantics.sound3313_e`, `OAI.MUB6.Certificate.PairSemantics.sound3314_e`, `OAI.MUB6.Certificate.PairSemantics.sound3315_e`, `OAI.MUB6.Certificate.PairSemantics.sound3316_e`, `OAI.MUB6.Certificate.PairSemantics.sound3317_e`, `OAI.MUB6.Certificate.PairSemantics.sound3319_e`, `OAI.MUB6.Certificate.PairSemantics.sound3322_e`, `OAI.MUB6.Certificate.PairSemantics.sound3324_e`, `OAI.MUB6.Certificate.PairSemantics.sound3325_e`, `OAI.MUB6.Certificate.PairSemantics.sound3326_e`, `OAI.MUB6.Certificate.PairSemantics.sound3327_e`, `OAI.MUB6.Certificate.PairSemantics.sound3328_e`, `OAI.MUB6.Certificate.PairSemantics.sound3331_e`, `OAI.MUB6.Certificate.PairSemantics.sound3333_e`, `OAI.MUB6.Certificate.PairSemantics.sound3334_e`, `OAI.MUB6.Certificate.PairSemantics.sound3335_e`, `OAI.MUB6.Certificate.PairSemantics.sound3336_e`, `OAI.MUB6.Certificate.PairSemantics.sound3338_e`, `OAI.MUB6.Certificate.PairSemantics.sound3339_e`, `OAI.MUB6.Certificate.PairSemantics.sound3341_e`, `OAI.MUB6.Certificate.PairSemantics.sound3343_e`, `OAI.MUB6.Certificate.PairSemantics.sound3345_e`, `OAI.MUB6.Certificate.PairSemantics.sound3346_e`, `OAI.MUB6.Certificate.PairSemantics.sound3347_e`, `OAI.MUB6.Certificate.PairSemantics.sound3348_e`, `OAI.MUB6.Certificate.PairSemantics.sound3349_e`, `OAI.MUB6.Certificate.PairSemantics.sound3350_e`, `OAI.MUB6.Certificate.PairSemantics.sound3351_e`, `OAI.MUB6.Certificate.PairSemantics.sound3352_e`, `OAI.MUB6.Certificate.PairSemantics.sound3353_e`, `OAI.MUB6.Certificate.PairSemantics.sound3354_e`, `OAI.MUB6.Certificate.PairSemantics.sound3355_e`, `OAI.MUB6.Certificate.PairSemantics.sound3356_e`, `OAI.MUB6.Certificate.PairSemantics.sound3357_e`, `OAI.MUB6.Certificate.PairSemantics.sound3358_e`, `OAI.MUB6.Certificate.PairSemantics.sound3359_e`, `OAI.MUB6.Certificate.PairSemantics.sound3360_e`, `OAI.MUB6.Certificate.PairSemantics.sound3361_e`, `OAI.MUB6.Certificate.PairSemantics.sound3362_e`, `OAI.MUB6.Certificate.PairSemantics.sound3363_e`, `OAI.MUB6.Certificate.PairSemantics.sound3364_e`, `OAI.MUB6.Certificate.PairSemantics.sound3366_e`, `OAI.MUB6.Certificate.PairSemantics.sound3367_e`, `OAI.MUB6.Certificate.PairSemantics.sound3368_e`, `OAI.MUB6.Certificate.PairSemantics.sound3369_e`, `OAI.MUB6.Certificate.PairSemantics.sound3370_e`, `OAI.MUB6.Certificate.PairSemantics.sound3371_e`, `OAI.MUB6.Certificate.PairSemantics.sound3372_e`, `OAI.MUB6.Certificate.PairSemantics.sound3375_e`, `OAI.MUB6.Certificate.PairSemantics.sound3376_e`, `OAI.MUB6.Certificate.PairSemantics.sound3377_e`, `OAI.MUB6.Certificate.PairSemantics.sound3378_e`, `OAI.MUB6.Certificate.PairSemantics.sound3380_e`, `OAI.MUB6.Certificate.PairSemantics.sound3382_e`, `OAI.MUB6.Certificate.PairSemantics.sound3383_e`, `OAI.MUB6.Certificate.PairSemantics.sound3384_e`, `OAI.MUB6.Certificate.PairSemantics.sound3385_e`, `OAI.MUB6.Certificate.PairSemantics.sound3387_e`, `OAI.MUB6.Certificate.PairSemantics.sound3388_e`, `OAI.MUB6.Certificate.PairSemantics.sound3389_e`, `OAI.MUB6.Certificate.PairSemantics.sound3390_e`, `OAI.MUB6.Certificate.PairSemantics.sound3391_e`, `OAI.MUB6.Certificate.PairSemantics.sound3392_e`, `OAI.MUB6.Certificate.PairSemantics.sound3393_e`, `OAI.MUB6.Certificate.PairSemantics.sound3394_e`, `OAI.MUB6.Certificate.PairSemantics.sound3395_e`, `OAI.MUB6.Certificate.PairSemantics.sound3396_e`, `OAI.MUB6.Certificate.PairSemantics.sound3397_e`, `OAI.MUB6.Certificate.PairSemantics.sound3399_e`, `OAI.MUB6.Certificate.PairSemantics.sound3400_e`, `OAI.MUB6.Certificate.PairSemantics.sound3401_e`, `OAI.MUB6.Certificate.PairSemantics.sound3402_e`, `OAI.MUB6.Certificate.PairSemantics.sound3405_e`, `OAI.MUB6.Certificate.PairSemantics.sound3407_e`, `OAI.MUB6.Certificate.PairSemantics.sound3408_e`, `OAI.MUB6.Certificate.PairSemantics.sound3411_e`, `OAI.MUB6.Certificate.PairSemantics.sound3412_e`, `OAI.MUB6.Certificate.PairSemantics.sound3413_e`, `OAI.MUB6.Certificate.PairSemantics.sound3414_e`, `OAI.MUB6.Certificate.PairSemantics.sound3415_e`, `OAI.MUB6.Certificate.PairSemantics.sound3416_e`, `OAI.MUB6.Certificate.PairSemantics.sound3417_e`, `OAI.MUB6.Certificate.PairSemantics.sound3418_e`, `OAI.MUB6.Certificate.PairSemantics.sound3419_e`, `OAI.MUB6.Certificate.PairSemantics.sound3420_e`, `OAI.MUB6.Certificate.PairSemantics.sound3421_e`, `OAI.MUB6.Certificate.PairSemantics.sound3422_e`, `OAI.MUB6.Certificate.PairSemantics.sound3423_e`, `OAI.MUB6.Certificate.PairSemantics.sound3424_e`, `OAI.MUB6.Certificate.PairSemantics.sound3425_e`, `OAI.MUB6.Certificate.PairSemantics.sound3428_e`, `OAI.MUB6.Certificate.PairSemantics.sound3431_e`, `OAI.MUB6.Certificate.PairSemantics.sound3433_e`, `OAI.MUB6.Certificate.PairSemantics.sound3434_e`, `OAI.MUB6.Certificate.PairSemantics.sound3435_e`, `OAI.MUB6.Certificate.PairSemantics.sound3436_e`, `OAI.MUB6.Certificate.PairSemantics.sound3437_e`, `OAI.MUB6.Certificate.PairSemantics.sound3439_e`, `OAI.MUB6.Certificate.PairSemantics.sound3440_e`, `OAI.MUB6.Certificate.PairSemantics.sound3441_e`, `OAI.MUB6.Certificate.PairSemantics.sound3442_e`, `OAI.MUB6.Certificate.PairSemantics.sound3443_e`, `OAI.MUB6.Certificate.PairSemantics.sound3444_e`, `OAI.MUB6.Certificate.PairSemantics.sound3447_e`, `OAI.MUB6.Certificate.PairSemantics.sound3449_e`, `OAI.MUB6.Certificate.PairSemantics.sound3451_e`, `OAI.MUB6.Certificate.PairSemantics.sound3454_e`, `OAI.MUB6.Certificate.PairSemantics.sound3455_e`, `OAI.MUB6.Certificate.PairSemantics.sound3456_e`, `OAI.MUB6.Certificate.PairSemantics.sound3457_e`, `OAI.MUB6.Certificate.PairSemantics.sound3458_e`, `OAI.MUB6.Certificate.PairSemantics.sound3459_e`, `OAI.MUB6.Certificate.PairSemantics.sound3460_e`, `OAI.MUB6.Certificate.PairSemantics.sound3461_e`, `OAI.MUB6.Certificate.PairSemantics.sound3462_e`, `OAI.MUB6.Certificate.PairSemantics.sound3463_e`, `OAI.MUB6.Certificate.PairSemantics.sound3467_e`, `OAI.MUB6.Certificate.PairSemantics.sound3468_e`, `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound101_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound102_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound103_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound104_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound105_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound106_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound107_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound108_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound112_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound116_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound117_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound118_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound119_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound120_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound121_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound123_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound124_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound128_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound129_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound131_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound132_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound133_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound134_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound135_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound136_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound142_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound145_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound146_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound147_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound148_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound149_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound14_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound150_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound152_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound154_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound155_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound156_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound157_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound158_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound159_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound15_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound160_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound161_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound162_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound164_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound165_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound166_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound167_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound168_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound170_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound171_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound172_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound174_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound175_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound177_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound178_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound179_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound180_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound181_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound182_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound183_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound185_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound186_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound187_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound189_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound18_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound190_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound191_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound192_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound193_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound194_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound195_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound196_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound197_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound198_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound200_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound202_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound203_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound204_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound205_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound206_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound208_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound209_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound210_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound211_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound212_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound215_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound216_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound217_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound218_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound219_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound220_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound221_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound222_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound223_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound224_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound225_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound227_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound228_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound229_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound230_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound231_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound232_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound233_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound234_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound235_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound237_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound238_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound239_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound240_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound241_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound242_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound243_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound246_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound247_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound248_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound249_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound250_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound251_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound252_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound253_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound254_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound26_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound27_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound29_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound30_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound31_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound32_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound34_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound35_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound36_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound37_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound38_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound39_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound40_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound41_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound42_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound43_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound44_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound45_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound46_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound47_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound49_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound50_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound51_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound52_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound53_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound54_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound55_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound56_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound59_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound60_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound61_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound62_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound63_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound64_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound65_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound66_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound67_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound69_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound70_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound72_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound73_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound74_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound75_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound77_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound78_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound79_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound80_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound81_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound82_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound83_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound84_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound85_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound86_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound87_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound88_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound89_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound8_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound90_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound93_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound95_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound96_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound98_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.PairSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.PairTargetSemantics.expandedIdentity1_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm11_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm12_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm13_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm14_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm16_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm17_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm18_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm19_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm21_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm22_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm23_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm24_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm25_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm26_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm6_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm7_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm8_e`, `OAI.MUB6.Certificate.PairTargetSemantics.weightedTerm9_e` and `OAI.MUB6.pair_cross_certificate_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw9step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw96Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw96step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw96step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw96step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw96step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw97 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw97Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw97step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw97step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw98 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw98Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw98step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw98step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw98step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw99 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw99Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw99step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw99step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw965Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw965step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw966step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw968Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw969 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw969step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw970 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw971Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw971step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw972 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw972step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw973 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw974 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw974Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw975 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw975step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw976 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw977 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw977Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw977step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw978 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw979 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw980 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw980Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw981 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw982 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw983 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw983Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw984 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw985 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw986 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw986Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw987 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw988 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw989Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw990 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw991 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw992Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw993 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw994 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw995 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw995Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw995step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw996 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw997 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw997step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw998 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw998Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw998step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]

def raw9657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9657step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9659step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9660step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9660step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9661step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9662step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9662step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9662step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9663 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9663step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9664step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9666step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9667step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9668step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9668step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9668step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9668step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9670step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9671step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9671step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9671step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9671step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9672step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9672step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9672step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9673step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw9675step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw9675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9676step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9676step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw9676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9678 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9679 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9679step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw9679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9680 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9680step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9681step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw9683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9684step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw9684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9696step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9696step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw9696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9699step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw9699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9700step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9700step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9700step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9700step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9700step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9701 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9702 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9703 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9703step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9704 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9704step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9705step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw9705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw9705step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw9705step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9708step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw9708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw9708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9709step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9715 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9716step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw9716step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9716step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw9716step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9719step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9719step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![1, -3, 2]]
def raw9720step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9720step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw9720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9720step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw9720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9723 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw9723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw9723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw9723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw9725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw9728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw9729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9730step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9730step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9730step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9733step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9733step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9733step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9734step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9734step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9734step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw9762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw9763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw9767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9793step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9793step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9793step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9794step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw9797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw9805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw9806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw9811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw9811step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw9813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw9813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw9815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw9815step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw9818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9826 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw9826step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9826step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9826step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw9844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw9846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9873step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9890step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9896step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9901step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9908step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9911step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9912step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9916 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9917 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9938 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9939 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9940 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9943 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9945 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9946 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9947 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9949 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9951 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9952 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9953 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9954 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9956 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9957 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9959 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9973step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw9995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw9995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw9998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall644 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall645 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall646 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall647 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall648 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall649 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall650 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall652 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall655 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1165 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1166 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1167 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1168 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1170 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1172 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1173 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1175 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1176 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1177 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1255 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1265 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1266 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1267 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1269 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1271 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1274 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1275 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1298 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1299 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1300 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1301 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1302 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1304 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1305 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1307 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1308 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1311 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1312 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1313 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1339 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1340 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1341 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1342 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1343 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1344 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1346 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1349 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1395 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1396 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1397 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1399 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1401 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1409 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1410 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1411 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1412 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1413 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1414 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1416 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1417 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1419 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1420 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1427 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1441 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1442 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1443 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1444 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1445 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1449 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1451 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1453 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1454 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1468 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1470 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1471 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1473 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1475 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1477 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1478 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1479 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall1480 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2357 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2358 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2359 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2363 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2527 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2528 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2530 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2531 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2532 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2570 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2572 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2574 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2576 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2593 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2594 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2595 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2596 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2598 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2599 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2601 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2602 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2604 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2605 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2636 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2637 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2638 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2640 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2642 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2644 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2753 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2755 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2766 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2767 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2768 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2770 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2775 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2776 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2778 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2784 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2788 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2828 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2829 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2832 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2901 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2903 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2904 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2936 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2937 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2939 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2941 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2943 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2957 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2958 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2959 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2960 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2961 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2963 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2965 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2966 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2968 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2969 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2986 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2987 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2988 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2990 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2991 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2996 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2997 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall2998 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3003 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3005 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3081 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3082 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3087 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3088 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3089 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3090 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3093 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3094 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3095 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3099 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3100 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3101 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3102 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3103 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3105 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3106 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3109 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3110 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3113 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3116 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3117 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3119 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3120 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3121 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3125 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3139 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3140 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3141 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3142 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3143 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3144 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3145 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3178 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3184 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3185 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3187 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3188 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3190 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3191 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3203 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3204 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3205 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3206 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3207 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3209 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3210 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3211 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3223 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3224 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3225 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3226 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3227 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3711 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3726 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3727 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3728 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3734 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3735 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3736 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3737 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3738 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3739 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3740 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3741 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3818 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3820 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3821 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3822 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3823 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3824 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3829 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3830 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3831 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3847 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3851 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3852 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3853 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3855 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3856 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3858 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3862 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3882 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3883 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3887 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3888 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3889 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3911 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3912 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3915 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3916 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3925 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3926 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3930 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3931 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3933 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3934 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3936 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3937 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3938 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3939 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3965 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3966 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3967 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall3969 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3970 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3977 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3980 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3981 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3982 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3984 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3987 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3990 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3992 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3993 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3994 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3995 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3997 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall3998 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4002 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4003 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4004 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4012 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4013 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4014 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4015 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4017 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4020 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4023 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4026 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4027 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4028 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4029 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4030 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4031 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4032 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4033 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4039 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4050 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4051 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4053 : Fin 2 → Fin 1 := ![0, 0]

def singletonSmall4093 : Fin 1 → Fin 1 := ![0]

def singletonSmall4094 : Fin 1 → Fin 1 := ![0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4096 : Fin 1 → Fin 1 := ![0]

def singletonSmall4098 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4099 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4100 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4101 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4102 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4103 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4104 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4105 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4106 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4107 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4108 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4109 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4110 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4111 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4112 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4113 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4115 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4119 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4121 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4122 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4126 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4128 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4132 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4133 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4134 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4138 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4139 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4140 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4141 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4142 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4143 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4144 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4145 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4146 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4147 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4148 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4164 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4165 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4166 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4167 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4168 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4171 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4172 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4174 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4175 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4177 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4180 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4181 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4182 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4183 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4185 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4186 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4187 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4190 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4191 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4192 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4194 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4195 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4196 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4197 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4198 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4199 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4200 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4201 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4202 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4203 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4204 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4205 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4207 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4210 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4212 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4213 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4217 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4219 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4223 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4224 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4225 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4229 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4230 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4231 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4232 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4233 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4234 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4235 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4236 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4237 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4238 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4239 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4240 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4241 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4242 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4243 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4248 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4249 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4251 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4252 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4253 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4255 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4256 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4257 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4265 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4268 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4270 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4272 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4275 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4276 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4278 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4279 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4280 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4285 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4286 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4287 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4288 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4289 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4290 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4291 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4292 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4293 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4294 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4295 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4296 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4298 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4301 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4303 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4304 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4307 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4309 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4313 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4314 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4315 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4319 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4320 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4321 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4322 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4323 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4324 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4325 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4337 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4338 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4339 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4341 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4343 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4344 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4346 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4349 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4350 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4351 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4352 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4354 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4355 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4356 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4359 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4360 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4361 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4396 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4398 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4399 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4401 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4404 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4405 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4417 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4418 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4419 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4421 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4424 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4428 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4431 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4451 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4452 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4454 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4456 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4457 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4458 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4460 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4461 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4463 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4466 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4467 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4468 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4489 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4490 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4491 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4493 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4495 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4496 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4499 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4503 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4507 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4510 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4513 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4514 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4515 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4516 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4517 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4518 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4519 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4520 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4521 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4522 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4523 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4524 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4525 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4526 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4537 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4538 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4539 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4541 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4543 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4544 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4546 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4549 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4550 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4551 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4553 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4554 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4555 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4557 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4558 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4559 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4569 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4570 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4572 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4575 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4581 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4583 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4586 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4601 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4602 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4605 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4606 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4608 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4612 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4618 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4619 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4621 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4622 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4623 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4624 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4625 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4627 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4628 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4629 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4630 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4631 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4632 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4633 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4634 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4635 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4636 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4637 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4638 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4640 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4642 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4644 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4645 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4648 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4650 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4653 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4654 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4657 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4658 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4660 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4661 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4672 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4673 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4676 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4678 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4679 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4681 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4684 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4685 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4686 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4688 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4689 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4691 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4692 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4693 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4706 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4707 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4709 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4710 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4713 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4716 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4717 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4719 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4720 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4721 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4722 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4723 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4724 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4725 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4726 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4727 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4728 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4729 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4731 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4732 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4737 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4740 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4742 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4744 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4746 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4747 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4749 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4750 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4754 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4759 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4760 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4763 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4764 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4766 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4767 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4769 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4770 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4778 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4779 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4782 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4787 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4788 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4798 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4800 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4801 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4802 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4804 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4805 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4807 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4810 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4811 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4826 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4827 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4828 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4831 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4832 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4835 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4839 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4843 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4845 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4859 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4860 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4862 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4864 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4865 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4866 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4868 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4869 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4871 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4874 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4875 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4887 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4888 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4889 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4890 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4896 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4898 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4899 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4902 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4907 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4913 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4926 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4927 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4928 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4936 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4937 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4939 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4941 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4943 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4946 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4947 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4948 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4949 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4950 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4952 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4953 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4960 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4961 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4967 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4968 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4969 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4970 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4971 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4972 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4973 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4974 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4977 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4979 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4985 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4986 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4987 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall4996 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall4998 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5000 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5003 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5013 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5014 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5015 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5018 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5021 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5023 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5030 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5032 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5033 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5036 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5037 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5038 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5039 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5047 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5050 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5055 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5056 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5059 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5070 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5072 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5073 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5075 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5076 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5078 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5080 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5081 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5093 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5094 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5095 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5098 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5099 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5102 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5105 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5109 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5110 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5114 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5117 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5123 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5125 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5126 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5134 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5137 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5141 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5142 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5149 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5152 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5155 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5156 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5162 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5163 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5167 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5168 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5169 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5170 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5171 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5172 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5174 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5176 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5177 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5192 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5193 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5202 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5203 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5204 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5207 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5227 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5228 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5237 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5238 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5241 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5247 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5248 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5257 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5258 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5259 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5261 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5271 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5272 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5275 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5284 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5290 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5291 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5292 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5293 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5294 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5296 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5301 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5302 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5304 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5305 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5306 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5310 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5328 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5329 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5333 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5335 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5336 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5337 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5341 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5344 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5346 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5349 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5351 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5352 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5354 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5355 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5356 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5363 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5364 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5365 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5368 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5370 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5372 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5373 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5374 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5378 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5380 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5383 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5384 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5386 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5387 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5388 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5389 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5390 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5391 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5393 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5395 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5397 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5398 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5400 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5401 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5403 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5404 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5405 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5406 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5411 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5412 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5415 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5416 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5417 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5418 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5422 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5423 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5424 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5428 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5431 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5432 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5433 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5434 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5435 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5437 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5438 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5439 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall5443 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5447 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5448 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5449 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5450 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5451 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5452 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5453 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5456 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5464 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5465 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5466 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5467 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5469 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5472 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5473 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5475 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5476 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5478 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5482 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5483 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5484 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5485 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5490 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5491 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5492 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5494 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5498 : Fin 2 → Fin 2 := ![0, 1]

def singletonSmall5500 : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1024 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def node1025 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def node1026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def node1027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def node1028 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def node1029 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

def node1030 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 4, -5]]

def node1031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node1032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node1033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1034 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

def node1035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def node1036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def node1037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def node1038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

def node1039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, 0, -2]]

def node1040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def node1041 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, 1, -2, 0]]

def node1042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def node1043 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node1044 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node1045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def node1046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, 0, 2, -3]]

def node1047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def node1048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node1049 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def node1050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def node1051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -4, 3], ![1, 0, 2, -3]]

def node1052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![1, 0, 1, -2]]

def node1053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def node1054 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node1055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -4, 2], ![1, -1, 2, -2]]

def node1056 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def node1057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node1058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def node1059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node1060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def node1061 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -4, 3], ![1, 0, 1, -2]]

def node1062 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

def node1063 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

def node1064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -4, 2], ![1, -1, 1, -1]]

def node1065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def node1066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def node1067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def node1068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node1069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, 0, -1, 0]]

def node1070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -2, 1]]

def node1071 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -1, -1, 1]]

def node1072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node1073 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node1074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node1075 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node1076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def node1077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, -2, 1], ![1, -1, 4, -4]]

def node1078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node1080 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def node1081 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node1082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2]]

def node1083 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def node1084 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def node1085 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def node1086 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

def node1087 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, 3, -4], ![0, 2, -2, 0], ![1, -2, -1, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node128 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, -1, 0], ![1, 1, -2]]

def node129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]

def node132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]

set_option maxHeartbeats 1000000 in
def node133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 3, -4], ![2, -2, 0]]

def node134 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]

def node135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 2, -3], ![2, -2, 0]]

def node136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 1, -2], ![2, -2, 0]]

def node137 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, -1, 0], ![2, -1, -1]]

def node138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 4, -3], ![1, 0, -1], ![2, -2, 0]]

def node139 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![2, 2, -4]]

def node140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 2, -2], ![2, 1, -3]]

def node141 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 3, -3], ![2, 0, -2]]

def node142 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def node143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def node144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 1, -2], ![1, 2, -3]]

def node145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def node147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

def node148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def node149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node150 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node151 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]

def node152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -2, 1], ![1, 2, -3]]

def node153 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node154 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -2, 1], ![1, 1, -2]]

set_option maxHeartbeats 1000000 in
def node155 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def node157 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node158 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 3, -4], ![2, -3, 1]]

def node159 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]

def node160 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 2, -3], ![2, -3, 1]]

def node161 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![1, -2, 1], ![2, -1, -1]]

def node162 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]

def node163 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 3, -3], ![2, 0, -2]]

def node164 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 4, -4], ![2, -1, -1]]

def node165 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, -1, 0], ![1, 4, -5]]

def node166 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

def node167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 1, -2], ![1, 2, -3]]

def node168 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

def node169 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]

def node170 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 3, -3], ![2, -1, -1]]

def node171 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 4, -4], ![2, -2, 0]]

def node172 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -2, 1], ![1, 4, -5]]

def node173 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def node174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

def node175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]

def node176 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def node178 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 3, -3], ![2, -3, 1]]

def node179 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -3, 2], ![1, 3, -4]]

def node180 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def node181 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node182 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![2, -3, 1]]

def node183 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -3, 2], ![1, 2, -3]]

def node184 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def node185 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def node187 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node188 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node189 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -3, 2], ![1, 0, -1]]

def node190 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def node191 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![1, -3, 2], ![2, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1472 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node1473 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1474 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1475 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node1476 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1477 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1478 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1479 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node1480 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def node1484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def node1485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def node1486 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def node1487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def node1489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def node1490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

def node1492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node1493 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def node1494 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def node1495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def node1496 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node1498 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def node1499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1503 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node1504 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1505 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1506 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1507 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node1508 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1509 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, -1, -1]]

def node1510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1516 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1517 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def node1518 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1519 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def node1523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node1526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node1527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node1528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node1529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def node1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def node1533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node1534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node1535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node1543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def node1544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 1, -3]]

def node1545 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def node1546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def node1548 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def node1549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node1550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node1551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def node1552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def node1553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node1554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node1556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node1557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1558 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node1564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def node1565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node1566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node1567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node1568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node1569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def node1570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def node1571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node1572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def node1575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node1578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node1582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

def node1583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, -1, -1, 0]]

def node1584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, 0, -3]]

def node1585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def node1586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -2, -1]]

def node1587 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def node1588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def node1589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node1590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def node1591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node1592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node1593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -2, 0]]

def node1594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node1595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1596 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node1597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node1599 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1664 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, -1, 1, -2]]

def node1665 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, -1, -2]]

def node1666 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def node1667 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def node1668 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

def node1669 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1670 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node1671 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def node1673 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 2, -1, -2]]

def node1674 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def node1675 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node1676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def node1677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node1678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node1679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node1680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node1681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def node1682 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node1683 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node1684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def node1685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node1686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1687 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1689 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node1690 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1691 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def node1692 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node1693 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node1694 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node1695 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node1696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node1697 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node1698 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1699 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def node1700 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node1701 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1706 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1707 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node1708 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def node1709 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node1710 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node1711 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1713 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1714 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node1715 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node1716 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node1717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node1718 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node1719 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1721 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def node1722 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1723 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1724 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def node1725 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def node1726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def node1729 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1731 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1734 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node1736 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node1737 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node1738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def node1739 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node1741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node1743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node1744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node1747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node1750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node1751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node1754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node1755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node1756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def node1757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node1758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node1759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node1760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node1765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node1766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node1767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node1768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node1769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def node1770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node1771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node1772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node1776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node1780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node1781 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node1782 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def node1783 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node1784 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node1785 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node1786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node1787 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -2, 1]]

def node1788 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def node1789 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node1790 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1791 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1792 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node1793 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1794 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node1795 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def node1796 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node1797 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1798 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1799 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node1800 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1801 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1802 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def node1803 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def node1806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def node1807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def node1808 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node1809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node1810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def node1811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node1812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -2, 0]]

def node1813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node1814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node1818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def node1823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1824 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node1825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1828 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def node1830 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node1831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node1832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def node1833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1834 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1835 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1836 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1837 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node1839 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node1840 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node1841 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node1842 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1843 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node1844 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node1845 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1846 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, -1, 0, -1]]

def node1847 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node1848 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node1850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node1851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node1852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def node1853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def node1854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node1855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node192 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 3, -3], ![2, 0, -2]]

def node193 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 4, -4], ![2, -1, -1]]

def node194 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, -1, 0], ![1, 4, -5]]

def node195 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 0, -1], ![1, 3, -4]]

def node196 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

def node197 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]

def node198 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 3, -3], ![2, -1, -1]]

def node199 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 4, -4], ![2, -2, 0]]

def node200 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -2, 1], ![1, 4, -5]]

def node201 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, -1, 0], ![1, 3, -4]]

def node202 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

def node203 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]

def node204 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

def node205 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -3, 2], ![1, 4, -5]]

def node206 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

def node207 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def node208 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -4, 3], ![1, 3, -4]]

def node209 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -3, 2], ![1, 2, -3]]

def node210 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node211 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -4, 3], ![1, 2, -3]]

def node212 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -3, 2], ![1, 1, -2]]

def node213 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -4, 3], ![1, 1, -2]]

def node214 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def node215 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def node216 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -4, 3], ![1, 0, -1]]

def node217 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -3, 2], ![1, -1, 0]]

def node218 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 4, -4], ![1, -2, 1], ![1, -2, 1]]

def node219 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -4, 4], ![1, 1, -2], ![1, 2, -3]]

def node220 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 3, -3], ![2, -1, -1]]

def node221 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, -1, 0], ![1, 3, -4]]

def node222 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 0, -1], ![1, 2, -3]]

def node223 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

def node224 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]

def node225 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

def node226 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -1, 0], ![1, 2, -3]]

def node227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]

def node228 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

def node229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

def node230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]

def node231 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]

def node232 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def node233 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 2, -3]]

def node234 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 2, -1], ![1, 1, -2], ![1, 1, -2]]

def node235 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 3, -2], ![1, 0, -1], ![1, 1, -2]]

def node236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 4, -3], ![1, 0, -1], ![1, 0, -1]]

def node237 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def node238 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 2, -2], ![1, 1, -2]]

def node239 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def node240 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 2, -2], ![0, 2, -2], ![1, 0, -1]]

def node241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 2, -3]]

def node242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 3, -4]]

def node243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3]]

def node244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2]]

def node245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 2, -3]]

def node246 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2]]

def node247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 1, -2]]

def node248 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1]]

def node249 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 4, -3], ![1, -1, 0], ![1, 0, -1]]

def node250 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 2, -2], ![1, 2, -3]]

def node251 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 3, -3], ![1, 1, -2]]

def node252 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def node253 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def node254 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node1985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node1986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node1987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node1988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, 0, -2, 0]]

def node1989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![1, 0, 3, -4], ![1, 1, -2, 0]]

def node1990 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node1991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node1992 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, 1, 2, -4]]

def node1993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1994 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1995 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node1996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1997 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1998 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node1999 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2000 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2001 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node2002 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def node2003 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node2004 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node2005 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2006 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def node2008 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -1, 1, -2]]

def node2009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node2010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node2011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2012 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 2, -3, 1], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def node2013 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node2014 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node2015 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node2016 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node2017 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2018 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node2019 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node2020 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node2021 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2022 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node2023 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def node2025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 2, -2]]

def node2026 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node2027 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node2028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def node2029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node2030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node2031 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node2032 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def node2033 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def node2034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node2035 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node2036 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node2037 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node2038 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2039 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node2040 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node2041 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node2042 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def node2044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node2045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node2046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2047 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2560 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2561 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2562 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node2563 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 0, 0, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node2564 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2565 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node2566 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2567 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2568 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2569 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node2570 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node2571 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2572 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def node2573 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node2574 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node2575 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node2576 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node2577 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node2578 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2579 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2580 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2581 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node2582 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node2583 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2584 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node2585 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2586 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2587 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2588 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2589 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def node2590 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2591 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node2592 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2593 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node2594 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node2595 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def node2596 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def node2597 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node2598 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2599 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def node2600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node2601 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node2602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node2603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def node2605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node2606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def node2607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node2608 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def node2609 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node2610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node2611 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def node2612 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def node2613 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2614 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def node2615 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node2616 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2617 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def node2618 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2621 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node2622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2624 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node2625 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2626 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node2627 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2628 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node2629 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2630 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node2631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2632 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2633 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2634 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

def node2635 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node2636 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node2637 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def node2638 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node2639 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node2640 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def node2641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node2642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node2644 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node2645 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2646 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node2647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node2649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node2650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node2651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node2657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node2658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node2659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def node2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def node2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def node2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def node2672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def node2673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def node2674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def node2676 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2677 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2678 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2679 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2680 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![-1, 1, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2682 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2683 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node2684 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def node2687 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node2753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def node2754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -2, 0], ![1, -1, 3, -3]]

def node2755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node2756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 2, -2]]

def node2758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def node2759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node2760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

def node2761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def node2762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node2763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def node2764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

def node2765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node2766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node2768 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def node2769 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node2770 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def node2771 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node2772 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node2773 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node2774 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node2775 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def node2776 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node2777 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2778 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node2779 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def node2780 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def node2781 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node2782 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -2, 3, -2]]

def node2783 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def node2784 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2785 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def node2786 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def node2787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node2788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node2789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node2790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node2791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node2792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def node2793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1]]

def node2795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node2799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def node2800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node2801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node2802 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -2, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2803 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2804 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node2805 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node2806 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def node2807 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def node2808 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node2809 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2810 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node2811 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2812 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node2813 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node2814 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node2815 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2816 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node2817 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def node2818 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def node2819 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def node2820 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def node2821 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def node2822 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def node2823 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

def node2824 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def node2825 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node2826 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def node2827 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def node2828 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node2829 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node2830 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node2831 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def node2832 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4]]

def node2833 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2834 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2835 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![-1, 1, 2, -2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2836 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node2837 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2838 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node2839 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2840 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2841 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2842 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def node2843 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def node2844 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node2845 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node2846 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def node2847 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def node2848 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def node2849 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node2850 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def node2851 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0]]

def node2852 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def node2853 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, -1, 2]]

def node2854 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def node2855 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def node2856 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def node2857 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

def node2858 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def node2859 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def node2860 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -3, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 0, 1]]

def node2861 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def node2862 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, -3, 4]]

def node2863 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node2864 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node2865 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2866 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2867 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2868 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2869 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node2870 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node2871 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node2872 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node2873 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2874 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node2875 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2876 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node2877 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2878 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2879 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3008 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3009 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3010 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def node3011 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3012 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3013 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node3014 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3015 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3016 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node3017 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3018 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3019 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def node3020 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node3021 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3022 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def node3023 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node3024 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node3025 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node3026 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node3027 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node3028 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node3029 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3030 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node3031 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node3032 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node3033 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3034 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3035 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node3036 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node3037 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3038 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def node3039 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node3040 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3041 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node3042 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3043 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3044 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node3045 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node3046 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3047 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node3048 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node3049 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3050 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3051 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3052 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node3053 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3054 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3055 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node3056 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node3057 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node3058 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def node3059 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node3060 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node3061 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node3062 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3063 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node3064 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node3065 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3066 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3067 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3068 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3069 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3070 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3071 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3136 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3137 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def node3138 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3139 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node3140 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3141 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def node3142 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3143 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node3144 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node3145 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def node3146 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node3147 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node3148 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def node3149 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node3150 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def node3151 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3152 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node3153 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node3154 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3155 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3156 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node3157 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3158 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3159 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node3160 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3161 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node3162 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node3163 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3164 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3165 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node3166 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node3167 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node3168 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node3169 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node3170 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node3171 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node3172 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node3173 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node3174 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node3175 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node3176 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node3177 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3178 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node3179 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node3180 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node3181 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node3182 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node3183 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node3184 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3185 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node3186 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node3187 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node3188 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node3189 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def node3190 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node3191 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node3192 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node3193 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3194 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3195 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node3196 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node3197 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node3198 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node3199 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node0 : Matrix (Fin 0) (Fin 0) ℤ := ![]

def node1 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]

def node2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]

def node3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]

def node10 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]

def node11 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]

def node12 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]

def node13 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]

def node14 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]

def node15 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]

def node16 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]

def node17 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]

def node18 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]

def node19 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]

def node20 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]

def node21 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]

def node22 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 3, -4], ![2, -4, 2]]

set_option maxHeartbeats 1000000 in
def node23 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]

def node24 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]

def node25 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]

def node26 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]

def node27 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]

def node28 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]

def node29 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

def node30 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

def node31 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]

def node32 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]

def node33 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![2, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1280 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node1281 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node1282 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def node1283 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def node1284 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node1285 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def node1286 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def node1287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 0, -1]]

def node1288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node1290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def node1291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node1292 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def node1294 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def node1295 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node1296 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node1297 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def node1298 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node1299 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node1300 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def node1301 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def node1302 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def node1303 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, -1, 3], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node1304 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node1305 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def node1306 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def node1307 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, -1, 0, 0]]

def node1308 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node1309 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node1310 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def node1311 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node1312 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, 0, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def node1313 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

def node1314 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def node1315 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, -1, 2]]

def node1316 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def node1317 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def node1318 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node1319 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node1320 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node1321 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -3, 3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def node1322 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

def node1323 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]

def node1324 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1325 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -4, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def node1326 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node1327 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node1328 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 2, -2]]

def node1329 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def node1330 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![-1, 1, -1, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node1331 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node1332 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node1333 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node1334 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def node1335 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def node1336 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def node1337 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -2, -1, 2]]

def node1338 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def node1339 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node1340 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node1341 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def node1342 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 3, -2]]

def node1343 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node2113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node2114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node2115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node2116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node2117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node2118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node2119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node2123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def node2124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 3, -4]]

def node2125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node2126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

def node2127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 3, -4]]

def node2128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node2129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node2131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node2132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node2133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def node2134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node2135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

def node2136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node2137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def node2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]

def node2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, -1, 0]]

def node2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1]]

def node2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]

def node2143 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 2, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2144 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2145 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node2146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 1, 0, -2]]

def node2147 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -3, 4], ![1, 0, 0, -1]]

def node2148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2149 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2150 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2151 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2152 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2153 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node2154 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def node2155 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def node2156 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node2157 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2158 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2159 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2160 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2161 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2162 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2163 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2164 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node2165 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node2166 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node2167 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2168 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node2171 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node2172 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2174 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2175 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node256 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0]]

def node257 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![0, 3, -3], ![1, -2, 1]]

def node258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 2, -3]]

set_option maxHeartbeats 1000000 in
def node259 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3]]

def node260 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 2, -3]]

def node261 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2]]

def node262 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 1, -2]]

def node263 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1]]

def node264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 2, -2], ![1, 2, -3]]

def node265 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 3, -3], ![1, 1, -2]]

def node266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -2, 2], ![0, 4, -4], ![1, 0, -1]]

def node267 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3]]

def node268 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2]]

def node269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def node270 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def node271 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node272 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1]]

def node274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1]]

def node275 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]

def node276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]

def node277 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 3, -3], ![1, 1, -2]]

def node278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -3, 3], ![0, 4, -4], ![1, 0, -1]]

def node279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2]]

def node280 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1]]

def node281 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 4, -4], ![1, -1, 0]]

def node282 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 5, -5], ![1, -2, 1]]

def node283 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2]]

def node284 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1]]

def node285 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0]]

def node286 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 4, -4], ![1, -2, 1]]

def node287 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def node288 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1]]

def node289 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 3, -3], ![1, 0, -1]]

def node290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -3, 3], ![0, 4, -4], ![1, -1, 0]]

def node291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1]]

def node292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0]]

def node293 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]

def node294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0]]

def node295 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]

def node296 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]

def node297 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node298 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def node299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node302 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]

def node303 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node304 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def node305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def node306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def node307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def node310 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def node311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]

def node312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]

def node313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def node314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def node315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def node316 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]

def node317 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def node318 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def node319 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node100 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]

def node101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]

def node102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

def node103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]

def node104 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 3, -4], ![2, -2, 0]]

def node105 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]

def node106 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]

def node107 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

def node108 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]

def node109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def node110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]

def node111 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def node112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -4, 2]]

def node113 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, -1, 0], ![1, 3, -4]]

def node114 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]

def node115 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -2, 1], ![1, 3, -4]]

def node116 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]

set_option maxHeartbeats 1000000 in
def node117 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]

def node118 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def node119 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def node120 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node121 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 3, -3], ![2, -1, -1]]

def node122 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node123 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node124 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node125 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]

def node126 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, -1, 0], ![1, 2, -3]]

def node127 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![-1, -1, 1, 1], ![1, 1, -1, -1], ![1, 1, -1, -1]]

def node1089 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, -1, 3], ![0, 2, 2, -4], ![1, 1, -2, 0]]

def node1090 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -2, 0, 2], ![0, 2, 2, -4], ![1, 1, -3, 1]]

def node1091 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 1, -2]]

def node1092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, 1, -1, -1]]

def node1093 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def node1094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node1095 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node1096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node1097 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -3, 1], ![1, 0, 3, -4]]

def node1098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 2, -3]]

def node1099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node1100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node1101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, -1, -1]]

def node1102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node1103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node1104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1105 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -1, 1, -1]]

def node1106 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 1, 0]]

def node1107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, 1, -1, -1]]

def node1108 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def node1109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node1110 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node1111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def node1112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def node1113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node1114 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def node1115 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -3, 2], ![1, 0, 3, -4]]

def node1116 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def node1117 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node1118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node1119 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def node1120 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

def node1121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -4, 3], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node1122 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node1123 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1124 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node1125 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 2, 2, -4], ![1, -2, 0, 1]]

def node1126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node1127 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -2, 1], ![0, 2, 2, -4], ![1, -2, -1, 2]]

def node1128 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def node1129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, -3, 3]]

def node1130 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]

def node1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -2, 1], ![1, 0, -1]]

def node1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

def node1135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]

def node1137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![1, 1, -2]]

def node1138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node1139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node1140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 4, -4], ![1, -2, 1], ![1, -1, 0]]

def node1141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

def node1142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]

def node1143 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]

def node1144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 4, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]

def node1145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 4, -4], ![1, 0, -1]]

def node1146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]

def node1147 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1]]

def node1149 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1]]

def node1150 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0]]

def node1151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node1153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def node1154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -2, -1, 3], ![0, 3, 1, -4], ![1, 0, -2, 1]]

def node1155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node1156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node1157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 3, 1, -4], ![1, -1, -1, 1]]

def node1158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -3, 3], ![0, 3, 1, -4], ![1, -2, 0, 1]]

def node1159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, 0, -2, 2], ![0, 3, 1, -4], ![1, -2, -1, 2]]

def node1160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 1, 1], ![0, 2, 0, -2], ![1, 0, 2, -3]]

def node1163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def node1164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node1165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node1166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node1167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node1168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1169 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

def node1170 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node1171 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node1172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def node1173 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

def node1174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node1175 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node1176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1177 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def node1178 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node1179 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 2, -1]]

def node1180 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def node1181 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def node1182 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node1183 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def node1184 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, 0, 1]]

def node1185 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node1186 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def node1187 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def node1188 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, -1, -1], ![1, 0, 2, -3]]

def node1189 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node1190 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node1191 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node1192 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node1193 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node1194 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 4, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node1195 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 2, -3]]

def node1196 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, -1, 2], ![0, 2, 0, -2], ![1, -1, 3, -3]]

def node1197 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node1198 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1199 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node1200 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def node1201 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node1202 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node1203 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node1204 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2]]

def node1205 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def node1206 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node1207 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node1208 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def node1209 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

def node1210 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def node1211 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node1212 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node1213 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def node1214 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node1215 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node1857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def node1858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node1859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]

def node1863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def node1864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def node1865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def node1866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node1867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node1868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def node1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node1872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node1873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]

def node1874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]

def node1875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 3, -4]]

def node1876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node1877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node1878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node1879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 4, -4], ![1, -1, 0], ![1, 0, -1]]

def node1880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node1881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]

def node1882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 2, -3]]

def node1883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node1884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node1885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node1886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1]]

def node1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]

def node1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]

def node1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

def node1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

def node1892 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node1893 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node1894 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node1895 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1896 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1897 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1898 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1899 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1900 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node1901 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node1902 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node1903 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

def node1904 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def node1905 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def node1906 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node1907 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node1908 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node1909 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def node1910 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node1911 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node1912 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1913 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1914 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1915 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1916 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1917 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1918 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 1, -1]]

def node1919 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -2, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2368 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2369 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2370 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -3, 3], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2371 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2372 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def node2373 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def node2374 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def node2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

def node2385 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def node2386 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2387 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2388 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def node2389 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -2, -1]]

def node2390 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node2391 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2392 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node2393 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node2394 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2395 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2396 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node2397 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2398 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node2399 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node2400 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2401 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2402 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2403 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2404 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def node2405 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node2406 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node2407 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, -1, -2]]

def node2408 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node2409 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2410 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node2411 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2412 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2413 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2414 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 3, -4]]

def node2415 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 2, -3]]

def node2416 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node2417 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node2418 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2419 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node2420 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node2421 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2422 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node2423 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node2424 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node2425 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2426 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2427 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2428 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2429 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def node2430 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node2431 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2432 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2433 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 1, 2, -4]]

def node2434 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 1, -3]]

def node2435 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 1, -2]]

def node2436 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node2437 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2438 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2441 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 2, -3]]

def node2442 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node2443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2445 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def node2447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def node2451 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 1, 0, -2]]

def node2455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node2456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 2, -3]]

def node2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]

def node2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]

def node2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1]]

def node2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

def node2465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def node2466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node2468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

def node2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 3, -2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 4, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]

def node2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]

def node2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 3, -3], ![1, 0, -1]]

def node2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

def node2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0]]

def node2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1]]

def node2481 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node2482 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, -1, 2, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node2483 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2484 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2485 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2486 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -1, -1]]

def node2487 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node2489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node2490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 1, -1, -1]]

def node2491 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 1, -2]]

def node2492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2493 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node2494 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2495 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

def node1001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -3, 1], ![1, 0, 2, -3]]

def node1002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 1, -2]]

def node1003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node1004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

def node1005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def node1006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

def node1007 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -3, 1], ![1, 0, 1, -2]]

def node1008 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node1009 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node1010 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def node1011 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, 0, -3, 2]]

def node1012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, 1, 0, -2]]

def node1013 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

def node1014 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -4, 2], ![1, 0, 1, -2]]

def node1015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -3, 1], ![1, 0, 0, -1]]

def node1016 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, 0, -2, 1]]

def node1017 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, 0, -3, 2]]

def node1018 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 3, -2, -1], ![1, -1, -1, 1]]

def node1019 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 1, -3, 2], ![1, 1, -1, -1]]

def node1020 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, 0, -3, 2]]

def node1021 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, 1, 0, -2]]

def node1022 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, 1, -1, -1]]

def node1023 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node1217 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -1, 1, -1]]

def node1218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 3, -3]]

def node1219 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def node1220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def node1221 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def node1222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node1223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def node1224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def node1225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node1226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, 0, 1]]

def node1227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def node1228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def node1229 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def node1230 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def node1231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node1232 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node1233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 2, 3, -5], ![1, 0, -2, 1]]

def node1234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node1235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node1236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -2, 3], ![0, 2, 2, -4], ![1, -1, 1, -1]]

def node1237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def node1238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

def node1239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

def node1240 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, 3, -5], ![1, -1, -1, 1]]

def node1241 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node1242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node1243 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, -1, -2, 2]]

def node1244 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 1, -2]]

def node1245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node1246 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node1247 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -2, 1]]

def node1248 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 2, -1], ![0, 2, 1, -3], ![1, -1, -2, 2]]

def node1249 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

def node1250 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

def node1251 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 4, -3], ![0, 2, -1, -1], ![1, -1, -2, 2]]

def node1252 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node1253 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -1, 2, -2]]

def node1254 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 4, -3]]

def node1255 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 3, -2]]

def node1256 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 2, -1]]

def node1257 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

def node1258 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -2, 0, 1]]

def node1259 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node1260 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def node1261 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 2, -2]]

def node1262 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1]]

def node1263 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 1, -1]]

def node1264 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node1265 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

def node1266 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 2, -2], ![0, 2, 1, -3], ![1, -2, -2, 3]]

def node1267 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def node1268 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1]]

def node1269 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -2, 0, 1]]

def node1270 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, -1, 2]]

def node1271 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, -2, 3]]

def node1272 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, -1, -1, 1]]

def node1273 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 4, -4], ![0, 2, -3, 1], ![1, -2, 0, 1]]

def node1274 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -2, 3, -2]]

def node1275 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -2, 1, 0]]

def node1276 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def node1277 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node1278 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node1279 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, -2, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1344 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 1, -1]]

def node1345 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0]]

def node1346 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1]]

def node1347 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node1348 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node1349 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1]]

def node1350 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1]]

def node1351 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def node1352 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -2, 0, 1]]

def node1353 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, 4, -4], ![0, 1, -3, 2], ![1, -2, 0, 1]]

def node1354 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

def node1355 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node1356 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node1357 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0]]

def node1358 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -2, 1, 1], ![0, 2, 1, -3], ![1, -1, -3, 3]]

def node1359 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -2, 3], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node1360 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

def node1361 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, -1, -2, 2]]

def node1362 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def node1363 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

def node1364 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -2, -3, 4]]

def node1365 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -3, 3], ![0, 1, 2, -3], ![1, -2, 0, 1]]

def node1366 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -2, -1, 2]]

def node1367 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, -2, 3]]

def node1368 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, -1, -1, 2], ![0, 1, 1, -2], ![1, -1, -2, 2]]

def node1369 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -3, 3], ![0, 1, 1, -2], ![1, -2, 0, 1]]

def node1370 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, -1, 2]]

def node1371 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, -2, 3]]

def node1372 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 2, -2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -3, -1, 3]]

def node1373 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -3, 3], ![0, 0, 4, -4], ![1, -2, 0, 1]]

def node1374 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, -1, 0], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def node1375 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -3, 3], ![0, 0, 3, -3], ![1, -2, 0, 1]]

def node1376 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

def node1377 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -2, -1, 2]]

def node1378 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 1, -2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, -2, 3]]

def node1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def node1380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node1381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node1382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def node1383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node1384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node1385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def node1386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def node1387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def node1388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def node1389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node1390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node1391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node1392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node1393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def node1394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node1395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node1396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node1397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def node1398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def node1399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def node1400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node1401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node1402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def node1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]

def node1404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]

def node1405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node1406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node1407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2880 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2881 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2882 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node2883 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def node2884 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node2885 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2886 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2887 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2888 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2889 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2890 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2891 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2892 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node2893 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2894 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2895 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def node2896 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def node2897 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def node2898 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2899 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def node2900 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def node2901 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node2902 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node2903 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node2904 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node2905 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def node2906 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def node2907 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node2908 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node2909 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node2910 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node2911 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2912 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def node2913 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node2914 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2915 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node2916 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2917 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node2918 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2919 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2920 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node2921 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2922 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2923 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, -1, 0, -1]]

def node2924 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -2, -1]]

def node2925 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node2926 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node2927 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node2928 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2929 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node2930 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2931 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2932 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2933 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node2934 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2935 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2936 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node2937 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2938 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2939 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node2940 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node2941 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def node2942 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2943 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2944 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node2945 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def node2946 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2947 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node2948 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2949 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node2950 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2951 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node2952 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2953 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def node2954 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def node2955 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2956 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2957 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2958 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def node2959 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node2960 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def node2961 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node2962 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2963 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2964 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node2965 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2966 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node2967 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node2968 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node2969 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2970 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2971 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2972 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node2973 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2974 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2975 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2976 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2977 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node2978 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node2979 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node2980 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def node2981 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def node2982 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node2983 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def node2984 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2985 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 2, -1, -2]]

def node2986 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 1, -2]]

def node2987 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2988 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2989 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node2990 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2991 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2992 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node2993 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node2994 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 0, -1]]

def node2995 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2996 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node2997 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node2998 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 0, -2]]

def node2999 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3000 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def node3001 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node3002 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3003 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3004 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3005 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3006 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node3007 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3328 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node3329 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def node3330 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3331 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node3332 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node3333 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node3334 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3335 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 2, 0, -3]]

def node3336 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node3337 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node3338 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def node3339 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node3340 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node3341 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node3342 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3343 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node3344 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3345 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node3346 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![-1, 1, 0, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node3347 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node3348 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node3349 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node3350 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node3351 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node3352 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node3353 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node3354 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node3355 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node3356 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3357 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3358 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3359 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node3360 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3361 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3362 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3363 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3364 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3365 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2689 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

def node2690 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0]]

def node2691 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 1, 0]]

def node2692 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 2, -1]]

def node2693 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -2, 1, 0]]

def node2694 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node2695 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2696 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2697 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2698 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2699 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2700 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2701 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2704 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2705 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2706 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def node2707 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node2708 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0]]

def node2709 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0]]

def node2710 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

def node2711 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node2712 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 0, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node2713 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2714 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2715 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def node2716 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2717 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2718 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2719 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 3, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2720 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2721 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2722 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 0, 1], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node2723 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

def node2724 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2725 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2726 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

def node2727 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, -1, 1]]

def node2728 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node2729 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def node2730 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2731 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2]]

def node2732 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -2, 1, 0]]

def node2733 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1]]

def node2734 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

def node2735 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1]]

def node2736 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -2, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, 0, -1]]

def node2737 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def node2739 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2742 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2743 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2744 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2745 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2746 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 3, -1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2747 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def node2748 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

def node2749 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def node2750 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

def node2751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, 2, -4], ![1, 0, -3, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3072 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node3073 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def node3074 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node3075 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3076 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3077 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3078 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node3079 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3080 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node3081 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3082 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3083 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3084 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3085 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3086 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node3087 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3088 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3089 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 0, -2]]

def node3090 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node3091 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node3092 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node3093 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node3094 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3095 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node3096 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3097 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node3098 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3099 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3100 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3101 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def node3102 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def node3103 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node3104 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node3105 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node3106 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node3107 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node3108 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node3109 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, 0, -1]]

def node3110 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -1, 0, -1]]

def node3111 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node3112 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3113 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3114 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3115 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node3116 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3117 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def node3118 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node3119 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def node3120 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3121 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3122 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node3123 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3124 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3125 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3126 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3127 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3128 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3129 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3130 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3131 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node3132 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node3133 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3134 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node3135 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]

def node1409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def node1410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def node1411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

def node1412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def node1413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node1414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]

def node1415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]

def node1416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]

def node1417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

def node1418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node1419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def node1420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]

def node1421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]

def node1422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]

def node1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

def node1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def node1425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]

def node1426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def node1427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def node1428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

def node1429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node1430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node1431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def node1432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node1433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]

def node1434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node1435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]

def node1436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node1437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node1438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node1439 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node1440 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def node1441 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def node1442 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1443 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def node1444 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node1445 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1446 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def node1447 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1448 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1449 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1450 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def node1451 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def node1452 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1453 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1454 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node1455 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def node1456 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def node1457 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def node1458 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def node1459 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node1460 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node1461 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def node1462 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node1463 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def node1464 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def node1465 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def node1466 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def node1467 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def node1468 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def node1469 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1470 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node1471 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node320 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]

def node321 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node322 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node323 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

def node324 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]

def node326 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]

def node327 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]

def node328 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]

def node329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node330 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]

def node331 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]

def node332 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]

def node333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]

def node334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]

def node335 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]

def node336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]

def node337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -2, 1]]

def node2242 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2243 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node2244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2245 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node2246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def node2247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2248 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2249 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2250 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node2251 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2252 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node2253 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node2254 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def node2255 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def node2256 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def node2257 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def node2258 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def node2259 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def node2260 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def node2261 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2262 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2263 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2264 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def node2265 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def node2266 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def node2267 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def node2268 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node2269 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -3, 3], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2270 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node2271 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node2272 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node2273 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node2274 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node2275 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2276 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2277 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

def node2278 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def node2279 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

def node2280 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![2, -2, -2, 2]]

def node2281 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def node2282 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def node2283 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node2284 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2285 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def node2286 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node2287 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def node2288 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def node2289 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def node2290 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def node2291 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def node2292 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def node2293 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node2294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def node2295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

def node2296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

def node2299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

def node2301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def node2302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 3, -4]]

def node2303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def node2049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -2, 1]]

def node2050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -2, 1]]

def node2051 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 0, -1, 0]]

def node2052 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -2, 1]]

def node2053 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node2054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def node2055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node2056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node2057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node2058 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -2, 3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node2059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 1, -1, -1], ![1, 1, 1, -3]]

def node2060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node2061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node2062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node2063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def node2065 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

def node2066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, -1, -2, 1]]

def node2067 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node2068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node2069 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node2071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2072 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node2073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2074 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def node2075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def node2076 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node2077 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node2078 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def node2079 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def node2080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def node2081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def node2082 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, -1, 1]]

def node2083 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def node2084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node2085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node2087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2088 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]

def node2090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]

def node2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def node2092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

def node2093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]

def node2094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]

def node2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]

def node2096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]

def node2097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]

def node2098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]

def node2099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

def node2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]

def node2101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

def node2102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]

def node2103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

def node2104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

def node2105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node2106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1]]

def node2107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]

def node2108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 4, -3], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

def node2109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]

def node2110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]

def node2111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3200 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node3201 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 2, -3]]

def node3202 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node3203 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node3204 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node3205 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node3206 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3207 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3208 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3209 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node3210 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3211 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node3212 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -2, 2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3213 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def node3214 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node3215 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3216 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3217 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3218 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -3, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3219 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3220 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -1, 2], ![1, 0, 0, -1]]

def node3221 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 3, -1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3], ![1, 0, 0, -1]]

def node3222 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3223 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def node3224 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node3225 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3226 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node3227 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node3228 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node3229 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -1, 0, -1]]

def node3230 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3231 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node3232 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3233 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3234 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3235 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3236 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3237 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3238 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3239 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3240 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def node3241 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def node3242 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3243 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node3244 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3245 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node3246 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

def node3247 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node3248 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3249 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node3250 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node3251 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3252 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3253 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3254 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3255 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node3256 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3257 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node3258 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def node3259 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node3260 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node3261 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node3262 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node3263 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node3264 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node3265 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def node3266 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3267 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3268 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node3269 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def node3270 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node3271 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3272 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node3273 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3274 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node3275 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3276 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3277 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node3278 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3279 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node3280 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3281 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3282 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node3283 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node3284 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node3285 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3286 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node3287 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node3288 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node3289 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node3290 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node3291 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node3292 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node3293 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def node3294 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def node3295 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def node3296 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node3297 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node3298 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3299 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node3300 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node3301 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node3302 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node3303 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3304 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node3305 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node3306 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node3307 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node3308 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node3309 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3310 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node3311 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3312 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3313 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3314 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node3315 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node3316 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node3317 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def node3318 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def node3319 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node3320 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def node3321 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node3322 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node3323 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node3324 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node3325 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node3326 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node3327 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

def node2305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

def node2306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def node2307 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2308 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node2309 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2310 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2311 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node2312 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -3, 4], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2313 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -2, 3], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node2314 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, -1, 2], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node2315 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, -1, 0, 1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node2316 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def node2317 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node2318 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node2319 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def node2320 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def node2321 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2322 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2323 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 1, 0, -2]]

def node2324 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -3, 4], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2325 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -2, 3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2326 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2327 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 3, -2], ![0, -1, -1, 2], ![0, 1, 0, -1], ![1, -1, -2, 2], ![1, 0, 0, -1]]

def node2328 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, -1, 0, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2329 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2330 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -3, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2331 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2332 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, -1, 3, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node2333 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node2334 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node2335 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, -1, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2336 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node2337 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node2338 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node2339 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node2340 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def node2341 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def node2342 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2343 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node2344 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2345 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, -1, 1]]

def node2346 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node2347 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2348 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, -1, 2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2349 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def node2350 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node2351 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![2, -2, 1, -1]]

def node2352 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, 0, 0]]

def node2353 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2354 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node2355 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2356 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2357 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2358 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![2, -2, -1, 1]]

def node2359 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, -1, 2, -2]]

def node2360 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def node2361 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def node2362 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, -1, 1], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, -1, -1, 1]]

def node2363 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, -1, 2, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node2364 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def node2365 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node2366 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node2367 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 2, 0, 0], ![0, -1, -3, 4], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 0, 1, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1600 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node1601 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node1602 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def node1603 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1604 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1605 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1606 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -1, 1, -2]]

def node1607 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node1608 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1609 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1610 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1611 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1612 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1613 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1614 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node1615 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def node1616 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def node1617 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1618 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1619 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node1620 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def node1621 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, 0, -2]]

def node1622 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, -1, 2], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1623 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def node1624 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def node1625 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node1626 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def node1627 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def node1628 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

def node1629 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, 1, 0, -3]]

def node1630 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def node1631 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def node1632 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def node1633 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def node1634 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def node1635 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def node1636 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def node1637 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def node1638 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def node1639 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

def node1640 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node1641 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1642 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def node1643 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def node1644 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node1645 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def node1646 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def node1647 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def node1648 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def node1649 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def node1650 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def node1651 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -2, 1], ![1, 1, 0, -2]]

def node1652 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def node1653 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def node1654 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def node1655 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def node1656 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1], ![1, 0, 0, -1]]

def node1657 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def node1658 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 2, 0, -3]]

def node1659 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 2, 0, -3]]

def node1660 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

def node1661 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

def node1662 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 2, -2], ![1, 0, 0, -1]]

def node1663 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -1, 1, -1], ![1, 0, 0, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2496 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2498 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

def node2500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -1, -1]]

def node2502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node2503 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2504 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

def node2505 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2506 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0]]

def node2507 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node2508 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1]]

def node2509 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, -1, 1, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def node2510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, -1, 1, 0], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def node2511 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, 0, -2]]

def node2512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def node2515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2516 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node2517 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2518 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node2519 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node2520 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2521 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def node2522 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2523 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 1, -2], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node2524 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2525 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, -1, 0], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def node2526 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 0, 0], ![0, 1, 0, -1], ![1, -1, 3, -3], ![1, 0, -2, 1]]

def node2527 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, -1, 0], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def node2528 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def node2529 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 0, 1], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2530 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 1, 0, -2]]

def node2531 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def node2532 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def node2533 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

def node2534 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1]]

def node2535 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

def node2536 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2537 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 1, -2, 0]]

def node2538 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def node2539 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0]]

def node2540 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

def node2541 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def node2542 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2543 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def node2544 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2545 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def node2546 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def node2547 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2548 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 3, -3]]

def node2549 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0]]

def node2550 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 1, -2, 0]]

def node2551 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def node2552 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1]]

def node2553 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, -1, 1]]

def node2554 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

def node2555 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def node2556 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

def node2557 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2]]

def node2558 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 2, -2]]

def node2559 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, -1, -1, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node1920 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node1921 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def node1922 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def node1923 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def node1924 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node1925 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, 1, -2]]

def node1926 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node1927 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node1928 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node1929 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node1930 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node1931 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, -2, 0, 0]]

def node1932 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node1933 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node1934 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node1935 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node1936 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node1937 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node1938 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node1939 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node1940 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -2, 1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def node1941 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def node1942 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node1943 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def node1944 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def node1945 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

def node1946 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node1947 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node1948 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def node1949 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node1950 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node1951 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node1952 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node1953 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node1954 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node1955 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def node1956 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node1957 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node1958 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node1959 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -2, 1, -1]]

def node1960 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node1961 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node1962 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def node1963 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def node1964 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node1965 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node1966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def node1967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node1968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node1969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node1970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node1971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node1972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node1973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node1974 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node1975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def node1976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node1977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node1978 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node1979 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 2, -2]]

def node1980 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, -1, 0]]

def node1981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

def node1982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node1983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 2, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Nodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

def node2176 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2178 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node2179 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def node2180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, 0, -2]]

def node2181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, 0, -2]]

def node2182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2183 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node2184 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -1, 1]]

def node2185 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node2186 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def node2187 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -1, 1]]

def node2188 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 0, 2, -2], ![1, -2, 0, 1], ![1, 1, -1, -1]]

def node2189 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node2190 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2191 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node2192 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node2193 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node2194 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 1, -1]]

def node2195 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 1, -1], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2196 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -2, 1, 0], ![1, 0, 0, -1]]

def node2197 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def node2198 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 0, -1, 0]]

def node2199 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2200 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2201 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -2, 3], ![0, 0, 3, -3], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2202 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def node2203 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def node2204 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

def node2205 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def node2206 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 1, -3]]

def node2207 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, -1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def node2208 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 2, -1], ![0, 0, 1, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def node2209 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def node2210 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def node2211 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def node2212 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def node2213 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def node2214 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def node2215 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node2216 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def node2217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def node2218 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def node2219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def node2220 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def node2221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 2, -1], ![1, 1, 1, -3]]

def node2222 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def node2223 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def node2224 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def node2225 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def node2226 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def node2227 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def node2228 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def node2229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 0, -1, 0]]

def node2230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 0, -1, 0]]

def node2231 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

def node2232 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def node2233 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def node2234 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 0, 0]]

def node2235 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -1, 1]]

def node2236 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -2, 2]]

def node2237 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 2, -2]]

def node2238 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

def node2239 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, 1, -1], ![0, 1, 1, -2], ![1, -2, 1, 0], ![1, 0, -2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix0 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

def boundaryMatrix1 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]

def boundaryMatrix2 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2]]

def boundaryMatrix3 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2]]

def boundaryMatrix4 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0]]

def boundaryMatrix5 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1]]

def boundaryMatrix6 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1]]

def boundaryMatrix7 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 0, 0]]

def boundaryMatrix8 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 1, 0]]

def boundaryMatrix9 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0]]

def boundaryMatrix10 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1]]

def boundaryMatrix11 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 2, 0, 0]]

def boundaryMatrix12 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 1, 0]]

def boundaryMatrix13 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 1, 0]]

def boundaryMatrix14 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 2, 0]]

def boundaryMatrix16 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix17 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3]]

def boundaryMatrix18 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2]]

def boundaryMatrix19 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

def boundaryMatrix20 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 3, -3]]

def boundaryMatrix21 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3]]

def boundaryMatrix22 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![2, 0, -2]]

def boundaryMatrix23 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![-3, 3, 0]]

def boundaryMatrix24 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, 2, 1]]

def boundaryMatrix25 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-2, 1, 1], ![-1, 2, -1]]

def boundaryMatrix26 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix27 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2]]

def boundaryMatrix28 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2]]

def boundaryMatrix29 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix30 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 2, 1, -1]]

def boundaryMatrix31 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 2, -1]]

def boundaryMatrix32 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, -1, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix269 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-3, 0, 3], ![1, 2, -3]]

def boundaryMatrix270 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![2, 1, -3]]

def boundaryMatrix271 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def boundaryMatrix273 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, 2, -1], ![2, 0, -2], ![-2, -1, 3]]

def boundaryMatrix275 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 4, -2]]

def boundaryMatrix276 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![-1, 4, -3]]

def boundaryMatrix277 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![-2, 4, -2]]

def boundaryMatrix278 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, 3, -4]]

def boundaryMatrix285 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![-2, 3, -1], ![2, 1, -3]]

def boundaryMatrix286 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1], ![1, -3, 2]]

def boundaryMatrix287 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -3, 2]]

def boundaryMatrix297 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 2, 2, -5]]

def boundaryMatrix298 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 1, 3]]

def boundaryMatrix300 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 0, 4]]

def boundaryMatrix301 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix302 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, -1, 4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix303 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2], ![-2, -2, 0, 4]]

def boundaryMatrix304 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, -1, 4]]

def boundaryMatrix305 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2], ![-2, -2, 0, 4]]

def boundaryMatrix306 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 1, -2], ![-2, -1, -1, 4]]

def boundaryMatrix307 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 2, 0, -3]]

def boundaryMatrix308 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryMatrix311 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![1, -1, 2, -2]]

def boundaryMatrix312 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryMatrix313 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

def boundaryMatrix314 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, -1, 1, 2], ![2, 1, 0, -3]]

def boundaryMatrix315 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, 1, 0, -3]]

def boundaryMatrix332 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 2, -2]]

def boundaryMatrix337 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 1, 1], ![-1, 2, 2, -3]]

def boundaryMatrix338 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix339 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix340 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1], ![-2, -2, 2, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix343 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 2, -2]]

def boundaryMatrix345 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 2, 2, -2]]

def boundaryMatrix346 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 2, 2, -3]]

def boundaryMatrix347 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![-1, 2, 2, -3]]

def boundaryMatrix349 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 0, 2], ![-2, 1, 3, -2]]

def boundaryMatrix350 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, -1, 2], ![-2, 1, 3, -2]]

def boundaryMatrix351 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix353 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 3, -3]]

def boundaryMatrix354 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix355 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, -2, 2]]

def boundaryMatrix356 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, -2, 3]]

def boundaryMatrix362 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 1, -2, 3]]

def boundaryMatrix363 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix364 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix365 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix368 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix369 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix372 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix373 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix374 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, 2, -2, 2]]

def boundaryMatrix377 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix378 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix379 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix381 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix382 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 1, 0], ![1, 1, 2, -4]]

def boundaryMatrix383 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 2, 0, 0], ![1, 0, 3, -4]]

def boundaryMatrix384 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 0, 2, -4]]

def boundaryMatrix385 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix386 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 0, 3, -4]]

def boundaryMatrix387 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix388 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, 1, 3, -4]]

def boundaryMatrix389 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 0, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix390 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix393 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![-2, 2, 0, 0], ![2, 0, 2, -4]]

def boundaryMatrix394 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 0, 1, 1], ![2, 1, 1, -4]]

def boundaryMatrix395 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-2, 1, 0, 1], ![2, 0, 2, -4]]

def boundaryMatrix396 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 0, 1, 1], ![1, 2, 1, -4]]

def boundaryMatrix397 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, 1, 2, -4]]

def boundaryMatrix398 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, 0, 0, 2], ![2, 0, 2, -4]]

def boundaryMatrix399 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![1, 1, 2, -4]]

def boundaryMatrix400 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 2, -4]]

def boundaryMatrix401 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, -1, 2, 0], ![1, 2, 1, -4]]

def boundaryMatrix402 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 1, 1], ![1, 1, 2, -4]]

def boundaryMatrix403 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![0, 2, 2, -4]]

def boundaryMatrix404 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, -1, 1], ![0, 1, 3, -4]]

def boundaryMatrix405 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-1, -1, 0, 2], ![1, 0, 3, -4]]

def boundaryMatrix406 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 0, 2], ![0, 1, 3, -4]]

def boundaryMatrix407 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, -1, 2], ![0, 1, 3, -4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix408 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![-1, -1, 2, 0], ![2, 1, 1, -4]]

def boundaryMatrix409 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 2, -1, 0], ![1, 0, 3, -4]]

def boundaryMatrix410 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-1, -1, 1, 1], ![2, 0, 2, -4]]

def boundaryMatrix412 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![1, 1, 2, -4]]

def boundaryMatrix419 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, -1, 2], ![1, -2, 2, -1]]

def boundaryMatrix422 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 1, 2], ![1, 1, 1, -3]]

def boundaryMatrix423 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 1, 2], ![0, 2, 1, -3]]

def boundaryMatrix425 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![1, -2, -1, 2]]

def boundaryMatrix430 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, -1, 2], ![0, 0, 3, -3]]

def boundaryMatrix433 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, -1, 3], ![2, -2, 1, -1]]

def boundaryMatrix434 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![-2, -1, 0, 3], ![2, -1, 1, -2]]

def boundaryMatrix436 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 2, 1, -2]]

def boundaryMatrix444 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![1, -1, 2, -2]]

def boundaryMatrix445 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![-2, -1, 0, 3], ![1, 0, 2, -3]]

def boundaryMatrix446 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 1, 2, -2]]

def boundaryMatrix447 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, -1, 0, 3], ![0, 1, 2, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix448 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, -1, 3], ![0, 1, 2, -3]]

def boundaryMatrix454 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 3, -1], ![-1, 0, -2, 3]]

def boundaryMatrix455 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, 3, -1], ![0, -1, -2, 3]]

def boundaryMatrix460 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def boundaryMatrix461 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix33 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix34 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 1, 2, -3]]

def boundaryMatrix35 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def boundaryMatrix36 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def boundaryMatrix37 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def boundaryMatrix38 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 1, 2, -3]]

def boundaryMatrix39 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def boundaryMatrix40 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 1, -3]]

def boundaryMatrix41 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -2, 0, 0]]

def boundaryMatrix42 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 0, 0]]

def boundaryMatrix43 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -2, 1, 0]]

def boundaryMatrix44 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 0, 1], ![1, -1, 1, -1]]

def boundaryMatrix45 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]

def boundaryMatrix46 : Matrix (Fin 7) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]

def boundaryMatrix47 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -2, 4]]

def boundaryMatrix48 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix49 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![1, 2, -3]]

def boundaryMatrix50 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]

def boundaryMatrix51 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![-2, -1, 3]]

def boundaryMatrix52 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-1, -1, 2], ![1, 2, -3]]

def boundaryMatrix53 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![0, 3, -3]]

def boundaryMatrix54 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]

def boundaryMatrix55 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 4, -3]]

def boundaryMatrix56 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 4, -4]]

def boundaryMatrix57 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![2, 1, -3]]

def boundaryMatrix58 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]

def boundaryMatrix59 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![-1, 3, -2]]

def boundaryMatrix60 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, 3, -3]]

def boundaryMatrix64 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]

def boundaryMatrix65 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]

def boundaryMatrix66 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2], ![-3, 2, 1]]

def boundaryMatrix67 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![-3, 1, 2]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix68 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, 1, 2]]

def boundaryMatrix69 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, 1, 2]]

def boundaryMatrix70 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, 0, 3]]

def boundaryMatrix71 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, 0, 3]]

def boundaryMatrix72 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def boundaryMatrix73 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]

def boundaryMatrix74 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1]]

def boundaryMatrix75 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2]]

def boundaryMatrix77 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1], ![-2, -2, 2, 2]]

def boundaryMatrix78 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, -2, 1, 3]]

def boundaryMatrix79 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 2, 2, -4]]

def boundaryMatrix80 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def boundaryMatrix81 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 2, -4]]

def boundaryMatrix82 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def boundaryMatrix83 : Matrix (Fin 7) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def boundaryMatrix84 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, 1, -1]]

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

def boundaryMatrix85 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 1, 2]]

def boundaryMatrix87 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 2, 1, -2]]

def boundaryMatrix88 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, 0, -2], ![-2, -1, 1, 2]]

def boundaryMatrix89 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryMatrix90 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, -1, 1, -1], ![-2, -1, 1, 2]]

def boundaryMatrix91 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![1, -1, 2, -2]]

def boundaryMatrix92 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, 0, 2], ![-1, 1, 2, -2]]

def boundaryMatrix93 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 0, 2], ![0, 1, 2, -3]]

def boundaryMatrix94 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 0, 2], ![2, -2, -1, 1]]

def boundaryMatrix95 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 0, 3]]

def boundaryMatrix96 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, -1, 3]]

def boundaryMatrix97 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 0, 3]]

def boundaryMatrix98 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 0, 3]]

def boundaryMatrix99 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![0, 2, -1, -1], ![-2, -1, 0, 3]]

def boundaryMatrix100 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def boundaryMatrix101 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 0, 3]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix102 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 0, 3]]

def boundaryMatrix103 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -1, 3]]

def boundaryMatrix104 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -1, 2, -1], ![-2, -1, 0, 3]]

def boundaryMatrix105 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 0, 2, -1], ![-1, -2, 0, 3]]

def boundaryMatrix106 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 0, 1], ![2, -1, 1, -2]]

def boundaryMatrix107 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![1, -1, 2, -2]]

def boundaryMatrix108 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, 0, 2], ![0, 2, 1, -3]]

def boundaryMatrix128 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 2, 2, -2]]

def boundaryMatrix129 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 1, 3, -2]]

def boundaryMatrix130 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 3, -2]]

def boundaryMatrix131 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-2, 2, 0, 0], ![2, -2, 1, -1]]

def boundaryMatrix133 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 1, 2, -1]]

def boundaryMatrix134 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![-2, 2, 0, 0], ![1, -1, 2, -2]]

def boundaryMatrix135 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1], ![-2, 2, 1, -1]]

def boundaryMatrix138 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -2, 0, 0], ![-2, 0, 3, -1]]

def boundaryMatrix139 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![-2, 1, 1, 0], ![1, -2, 2, -1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix140 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![-2, 1, 1, 0], ![1, -1, 2, -2]]

def boundaryMatrix144 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![0, 0, 2, -2], ![-2, 2, 1, -1]]

def boundaryMatrix145 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 0, 2, -1], ![-1, 2, 1, -2]]

def boundaryMatrix146 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-2, 0, 2, 0], ![0, 2, 1, -3]]

def boundaryMatrix147 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 1, -1], ![-1, 1, 2, -2]]

def boundaryMatrix150 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-2, 1, 1, 0], ![2, -2, -1, 1]]

def boundaryMatrix151 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![-2, 0, 2, 0], ![2, -2, -1, 1]]

def boundaryMatrix152 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, -1, -1, 0], ![-2, -1, 2, 1]]

def boundaryMatrix153 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![1, -2, 2, -1]]

def boundaryMatrix156 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![-2, 0, 1, 1], ![2, -2, 1, -1]]

def boundaryMatrix157 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -1, 0, -1], ![-2, -1, 2, 1]]

def boundaryMatrix158 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 1, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix161 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, 1, 1], ![-1, 2, 1, -2]]

def boundaryMatrix162 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, 2, 0, -2], ![-2, -1, 2, 1]]

def boundaryMatrix165 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -2, 0, 1], ![-2, 0, 3, -1]]

def boundaryMatrix166 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, -1, 1, -1], ![-2, -1, 2, 1]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix167 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 1, 1], ![-2, 1, 2, -1]]

def boundaryMatrix168 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -2, 3, -1]]

def boundaryMatrix169 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![-1, 1, 1, -1], ![-1, -2, 2, 1]]

def boundaryMatrix171 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix173 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 1, 0, 1], ![0, -1, 3, -2]]

def boundaryMatrix175 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![-2, 0, 2, 0], ![1, -2, -1, 2]]

def boundaryMatrix176 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1], ![0, -2, 2, 0], ![-2, 1, -1, 2]]

def boundaryMatrix183 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![0, -1, -1, 2], ![-2, 0, 3, -1]]

def boundaryMatrix184 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix187 : Matrix (Fin 7) (Fin 4) ℤ := ![![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def boundaryMatrix240 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 4, -5]]

def boundaryMatrix241 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]

def boundaryMatrix242 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![1, 3, -4]]

def boundaryMatrix243 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, 4, -3]]

def boundaryMatrix244 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-2, 0, 2], ![0, 4, -4]]

def boundaryMatrix245 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -2, 4]]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Boundary9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

def boundaryMatrix246 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, -1, 2], ![0, 4, -4]]

def boundaryMatrix247 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-2, -1, 3], ![1, 2, -3]]

def boundaryMatrix248 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, -2, 3], ![-1, 3, -2]]

def boundaryMatrix249 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -1, 3], ![0, 3, -3]]

def boundaryMatrix250 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![2, 1, -3]]

def boundaryMatrix251 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3], ![1, 2, -3]]

def boundaryMatrix252 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 3, -2], ![0, -3, 3]]

def boundaryMatrix253 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-1, -2, 3], ![0, 3, -3]]

def boundaryMatrix261 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]

def boundaryMatrix262 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -1, 4]]

def boundaryMatrix263 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def boundaryMatrix264 : Matrix (Fin 7) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![2, 2, -4]]

def boundaryMatrix265 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-3, 1, 2], ![3, 0, -3]]

def boundaryMatrix266 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![-3, 1, 2], ![2, 1, -3]]

def boundaryMatrix267 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-3, 1, 2], ![1, 2, -3]]

def boundaryMatrix268 : Matrix (Fin 7) (Fin 3) ℤ := ![![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-3, 0, 3], ![2, 1, -3]]

end MUB6.Certificate.PairSemantics

end OAI
end


