-- Prove2me | Definitions.Def_OAIQ106E116
-- name    : OAIQ106E116
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:24:12.22628+00:00
-- url     : https://prove2.me/theorems/19ede8e3-9a8d-429d-bb52-40ff38220dbb
-- title:
--   Definitions bundle OAIQ106E116 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7527 declarations of OpenAI's Lean: 7527 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw590step1`, `OAI.MUB6.Certificate.MixedSemantics.raw591`, `OAI.MUB6.Certificate.MixedSemantics.raw591Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw591step0`, `OAI.MUB6.Certificate.MixedSemantics.raw591step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw591step1`, `OAI.MUB6.Certificate.MixedSemantics.raw591step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw592`, `OAI.MUB6.Certificate.MixedSemantics.raw5922`, `OAI.MUB6.Certificate.MixedSemantics.raw5922Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step0`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step1`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step2`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step3`, `OAI.MUB6.Certificate.MixedSemantics.raw5922step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5923`, `OAI.MUB6.Certificate.MixedSemantics.raw5923Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step0`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step1`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step2`, `OAI.MUB6.Certificate.MixedSemantics.raw5923step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5924`, `OAI.MUB6.Certificate.MixedSemantics.raw5924Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step0`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step1`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step2`, `OAI.MUB6.Certificate.MixedSemantics.raw5924step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5925`, `OAI.MUB6.Certificate.MixedSemantics.raw5925Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5925step0`, `OAI.MUB6.Certificate.MixedSemantics.raw5925step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw5925step1`, `OAI.MUB6.Certificate.MixedSemantics.raw5925step1Labels` and 7487 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical4`, `MutuallyUnbiased_MixedSemantics_Canonical46`, `MutuallyUnbiased_MixedSemantics_Canonical47`, `MutuallyUnbiased_MixedSemantics_Canonical48`, `MutuallyUnbiased_MixedSemantics_Canonical49`, `MutuallyUnbiased_MixedSemantics_Canonical5`, `MutuallyUnbiased_MixedSemantics_Canonical50`, `MutuallyUnbiased_MixedSemantics_Canonical51`, `MutuallyUnbiased_MixedSemantics_Canonical52`, `MutuallyUnbiased_MixedSemantics_Canonical53`, `MutuallyUnbiased_MixedSemantics_Canonical54`, `MutuallyUnbiased_MixedSemantics_Canonical55`, `MutuallyUnbiased_MixedSemantics_Canonical56`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3980_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3981_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3982_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3984_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3990_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3992_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3994_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3995_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3998_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4003_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4023_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4026_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4031_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4032_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4033_e`, `OAI.MUB6.Certificate.MixedSemantics.sound4053_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound683_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound707_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound727_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound834_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound878_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound887_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound888_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound891_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound981_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`.
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

def raw5Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw5step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw6 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw6Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw6step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw6step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw59Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw59step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw59step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw60 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw60Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw60step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw60step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw60step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw60step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw61 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw61Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw61step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw61step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw62 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw62Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw62step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw62step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw62step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw62step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw63 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw63Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw63step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw63step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw64 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 4, -3]]
def raw64Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw64step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw64step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw64step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw64step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw65 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 4, -3]]
def raw65Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw65step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw65step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw65step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw65step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw72 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

def raw591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw591Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw591step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw591step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw593Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw593step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw594 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw595 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw595Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw595step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw595step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw596 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw597 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw597Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw597step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw597step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw598 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw599 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw599Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw599step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw600 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2]]
def raw600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw600step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw601 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2]]
def raw601Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw601step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw601step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw603Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw603step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw603step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw605Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw605step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw606 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw607 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw607Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw607step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw608 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw609Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw609step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw610 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw611 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw611Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw611step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw611step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw612 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw613 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw613Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw613step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw614 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw615 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw615Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw615step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw617Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw617step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw618 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw619 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw619Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw619step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw619step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw620 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw620step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw621 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw621Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw621step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw622 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw623 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw623Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw623step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw624 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw625 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw625Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw625step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw626 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 2, -1]]
def raw626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw627 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 2, -1]]
def raw627Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw627step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw627step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw628 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw629 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw629Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw629step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw629step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw630 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0]]
def raw630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw630step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw631 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0]]
def raw631Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw631step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw631step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw632 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 1, 1]]
def raw632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw632step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw632step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw633 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 1, 1]]
def raw633Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw633step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw633step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw635Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw635step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw637Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw637step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw637step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw638 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw639 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw639Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw639step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw639step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5922step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw5922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5925step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5925step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5926step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw5936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw5941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw5943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw5946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw5946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw5948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw5951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5952step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw5952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5952step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw5952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5955step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5955step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5956step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5957step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw5957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5957step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5957step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5957step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5957step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5960step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw5960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5960step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5960step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5960step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5961step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw5962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw5967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5969step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5970step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw5972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw5972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5973step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw5976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw5977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw5977step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw5977step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5978step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw5978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5978step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw5978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw5981step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5981step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5981step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5981step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw5986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw5986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5988 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![2, -2]]
def raw5988Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![2, -2]]
def raw5988step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]
def raw5988step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw5988step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw5992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw5998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw5999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw6000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw6000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw6001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw6001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw6001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw6004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw6004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw6007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw6009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw6009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw6009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6013step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw6015step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6015step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw6015step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6015step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw6015step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6016step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6017step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6018step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6018step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6018step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6023step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6038step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6039step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6039step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6039step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6043 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6045 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw6045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6070 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6070step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6071 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6072 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6073 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6074 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw6074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw6074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw6075step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6075step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw6075step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6076step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6078step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6078step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6078step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6079step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6079step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6079step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6085 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6085step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6086step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6090 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6090step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6090step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6096step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6099step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw6100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw6101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6102 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6103 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw6105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6111 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw6113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6117 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw6121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw6121step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw6124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw6124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw6156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw6181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw6183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw6184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw6185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw6185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw6193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw6198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6200step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw6209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6209step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6209step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw6211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw6211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw6221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6222 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw6222Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6222step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw6222step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6222step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6222step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw6245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw6315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw6315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw6315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw6316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw6316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6316step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw6316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6320step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6323step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6323step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6323step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6324step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6324step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw6327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw6328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6328step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6328step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw6329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw6329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw6331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw6331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6334step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6334step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6335step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw6336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw6337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6337step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6337step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw6339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw6342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw6342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6344 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]
def raw6344Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw6344step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw6344step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw6344step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw6356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 2, 1]]
def raw6357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw6357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw6367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw6367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6371 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6371step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6373step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6373step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6373step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6374step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6375step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6375step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6376step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6379step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6384step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6386step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6390 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6390step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6393 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw641 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw641Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw641step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw642 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw643 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw643Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw643step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw644 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw645 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw645Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw645step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw647Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw647step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw649Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw649step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw651Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw651step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw652 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw653 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw653Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw653step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw654 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw655 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw655Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw655step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw655step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw657Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw657step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw659Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw659step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw660 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw660Labels : Fin 2 → Fin 2 := ![0, 1]

def raw661 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw661Labels : Fin 2 → Fin 1 := ![0, 0]

def raw662 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw662Labels : Fin 2 → Fin 2 := ![0, 1]

def raw663 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw663Labels : Fin 2 → Fin 1 := ![0, 0]

def raw664 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw664Labels : Fin 2 → Fin 2 := ![0, 1]

def raw665 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw665Labels : Fin 2 → Fin 1 := ![0, 0]

def raw666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw668Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw668step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw669 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw669step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw670 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw671 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw671Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw671step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw671step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw674Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw675 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw676 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw677 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw677Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw677step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw678 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw678step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw679 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw680 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw680Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw680step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw681 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw681step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw681step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw682 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw682step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw683 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw683Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw683step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw683step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw683step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw684step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw686Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw686step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw686step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw687 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw688 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw689 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw689Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw689step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw689step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw690 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw690step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw691 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw692 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw692Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw693 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw693step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw694 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw695 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw695Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw695step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw696 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw696step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw696step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw697 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw697step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw698 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw698Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw698step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw699 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw699step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw699step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw700 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw700step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw701 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw701Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw701step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw702 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw702step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw702step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw703 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw703step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw704 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw704Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw704step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw705 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw705step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw705step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw706 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw706step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw707 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw707Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw707step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw707step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw708 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw708step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw708step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw708step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw709 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw709step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw710 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 0, -1], ![-2, 5, -3]]
def raw710Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw710step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw710step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw711step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw713Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw717 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw717step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw718 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw719 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw719Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw723 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw723step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw724 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw725 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw725Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw725step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw726 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw726step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw726step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw727 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw727step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw728 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6418 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6419step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6420 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw6420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw6420step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6421step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6422 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw6425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6428 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6430 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6433step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw6436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw6436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6440 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw6440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw6445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6450 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6452 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6455 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw6512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw6516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw6516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6516step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw6516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6522step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6523step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6524step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6525step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6525step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6525step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw6527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6527step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6528step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw6529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6531step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6532step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6533step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6533step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6535step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6536step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6536step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6537step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6539step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw6542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw6545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw6546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw6546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6546step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw6550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6553 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw6553Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw6553step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw6553step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6553step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw6576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw6608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw6609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw6610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw6611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw6617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw6631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw6636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw6637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw6637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw6673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6674 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![1, -1], ![1, -1]]
def raw6674Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6674step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]
def raw6674step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6674step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw6674step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw6683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw6685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw6687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw6687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw6699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6700step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6701 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6701step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6702 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6702step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6703 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6703step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6704 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6705step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6705step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6705step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6705step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6707step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6708step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6709step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6710step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6710step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6711step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6712step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6713step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6714step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw6715step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6715step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6716step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6718step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw6719step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6719step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6719step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6720step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6720step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6720step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6721step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6722step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6723step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6723step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6724step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6725 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6725step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6726step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6727step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6728 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6729 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6730 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6731 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6732 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6736 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6736step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6737step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6740 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw6743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6744 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6745 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw6745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw6747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6751 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6752 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6753 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6754 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6755 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6756 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6757 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6758 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw6765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw6765step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6766 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw6766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6775 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6777 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6782 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6784 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw6792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw6796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw6796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw6798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw6803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6806 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6807 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw6868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw6872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw6872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6877step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6879step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6883step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6883step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6883step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6885step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6885step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6886step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6887step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6889step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6889step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6891step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6891step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6894step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6894step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6894step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6894step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6897step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6897step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw6898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw6898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6901step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6909 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw6909Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw6909step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw6909step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6909step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw6916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6964step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6969step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw6980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw6989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw6990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw6990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw6990step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6994step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw6998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw6998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw6998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6999step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw6999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6999step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6999step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6999step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw7006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw7007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw7007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw7009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw7009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7013step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7013step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw7014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw7014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw7014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7016step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7017step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7018step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw7019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw7019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw7020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw7020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw7020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw7020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7020step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7020step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7020step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw7022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw7024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw7025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw7025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw7025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7027 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]
def raw7027Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![2, -2]]
def raw7027step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]
def raw7027step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw7027step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw7035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw7035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw7038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw7040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw7040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw7044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7053 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7053step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7053step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7053step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7053step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7054step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7054step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7063step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7067 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7078 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7079 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7080 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7081 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7081step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7081step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7081step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7081step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7084 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7093 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7094 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw7097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7166step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw7168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7171step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7171step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7171step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw7175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7175step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw7180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7181step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw7183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw7188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7188step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7199 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw7199Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7199step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7199step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7221step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7222 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7222step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7223 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7223step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7224 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7224step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7225step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7226step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7227 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7227step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7227step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7228step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7229 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7229step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7230step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7231step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7232 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7232step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7232step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7232step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7233 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7233step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7234step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7235step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7235step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7235step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7237step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7238step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7239 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7240 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7241 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7242 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7245 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw7249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7251 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7253 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7257 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7258 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7258step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7260 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7261step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7261step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7261step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7263 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw7263step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7267step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw7267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7268 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7268step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7275 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7277 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7278 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7279 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7280 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7283step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


