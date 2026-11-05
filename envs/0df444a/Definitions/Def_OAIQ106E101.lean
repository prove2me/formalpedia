-- Prove2me | Definitions.Def_OAIQ106E101
-- name    : OAIQ106E101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:12:04.333207+00:00
-- url     : https://prove2.me/theorems/eec27443-80e6-42e5-94fd-6507d98b2b1b
-- title:
--   Definitions bundle OAIQ106E101 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7495 declarations of OpenAI's Lean: 7495 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw25465step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25466`, `OAI.MUB6.Certificate.MixedSemantics.raw25466Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25466step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25466step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25466step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25466step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25467`, `OAI.MUB6.Certificate.MixedSemantics.raw25467Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25467step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25467step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25467step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25467step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25468`, `OAI.MUB6.Certificate.MixedSemantics.raw25468Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25468step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25468step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25468step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25468step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25469`, `OAI.MUB6.Certificate.MixedSemantics.raw25469Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25469step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25469step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2546Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2546step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2547`, `OAI.MUB6.Certificate.MixedSemantics.raw25470`, `OAI.MUB6.Certificate.MixedSemantics.raw25470Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25470step0`, `OAI.MUB6.Certificate.MixedSemantics.raw25470step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25470step1`, `OAI.MUB6.Certificate.MixedSemantics.raw25470step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25471`, `OAI.MUB6.Certificate.MixedSemantics.raw25471Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw25471step0` and 7455 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical1`, `MutuallyUnbiased_MixedSemantics_Canonical19`, `MutuallyUnbiased_MixedSemantics_Canonical198`, `MutuallyUnbiased_MixedSemantics_Canonical199`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical20`, `MutuallyUnbiased_MixedSemantics_Canonical200`, `MutuallyUnbiased_MixedSemantics_Canonical201`, `MutuallyUnbiased_MixedSemantics_Canonical202`, `MutuallyUnbiased_MixedSemantics_Canonical203`, `MutuallyUnbiased_MixedSemantics_Canonical204`, `MutuallyUnbiased_MixedSemantics_Canonical205`, `MutuallyUnbiased_MixedSemantics_Canonical206`, `MutuallyUnbiased_MixedSemantics_Canonical207`, `MutuallyUnbiased_MixedSemantics_Canonical208`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1164_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5476_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5482_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5483_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5485_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5490_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5492_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound95_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound682_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound694_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound726_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound890_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound980_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound982_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`.
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

def raw25Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw25step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw26 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw255 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw255step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2546Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw2546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2547 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2549Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw2549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2552Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2553 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2554 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2555 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2555Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2556 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2558Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2559 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2559step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]

def raw25466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25471step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw25475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25478step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25478step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw25481step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25481step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25481step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25485step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25486step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25488step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25494 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25494step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw25497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25497step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25499 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw25502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw25503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw25504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw25504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25511 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw25511Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25511step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25511step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25511step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25522 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![0, 0], ![1, -1]]
def raw25522Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw25522step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25522step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25522step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25529 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25529step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw25529step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw25546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25555 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw25555Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw25555step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25555step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25555step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw25566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25573 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw25573Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![0, 0], ![3, -3]]
def raw25573step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25573step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25573step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25573step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw25588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, -1, 1], ![2, -1, -1]]
def raw25589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, -2, 1], ![1, 0, -1]]
def raw25590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25591 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![-1, 1], ![1, -1]]
def raw25591step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25591step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25591step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw256 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw257 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw257step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw258 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw259 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw259step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw259step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw260 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw260step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw261 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw261step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw261step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw262 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw263 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw263Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw263step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw264 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw265 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw265Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw265step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw266 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw267 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2560 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2560step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2561 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2561Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2563 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2564Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2565 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2566 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2567 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2568 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2569 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2570 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2570step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2573Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2574 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2575 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2576 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2576Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2577 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2578 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2579 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2579Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2582Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2585Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2585step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2588Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2589 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2590 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2591 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2591Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2591step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2592 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2593 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2594 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2594Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2597Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2600Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2603Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2604 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2605 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2606 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2606Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2607 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2608 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2609 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2609Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2610 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2611 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2612 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2612Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2617 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2618 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2619 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2621 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2621Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2622 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2623 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2624 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2624step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2624step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2631step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2631step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2631step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2631step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2632step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2632step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2633step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2633step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2633step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw2634step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2634step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2634step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2634step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2634step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]
def raw2635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2635step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2635step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2635step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2637step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2637step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2638step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2638step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2639step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2639step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2639step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2639step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2640step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2642step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2642step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2642step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2643step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2643step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2643step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2644step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2644step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2644step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2644step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2645step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2647step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2647step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2648step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2648step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2649step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2649step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2649step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2649step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2650step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, -1, 0]]
def raw2655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2655step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2655step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2655step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2655step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2655step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw2656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw2656step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2656step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2656step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2656step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2657step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2657step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2658step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2658step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2658step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2659step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2660step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2660step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2662step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2663step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2664step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2665step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2665step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2665step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2667step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2668step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2669step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2672step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2674step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical200
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25607step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25607step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw25632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25634step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25635step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25635step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25636step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25637step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25641step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw25645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25648step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25648step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25648step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25648step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25649step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25649step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw25650step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw25650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25650step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw25650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw25651step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25651step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25651step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25651step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw25652step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25652step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25652step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25652step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25653step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25653step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25653step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25654step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25655step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25655step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw25656step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw25657step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25657step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25658step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25658step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25659step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25659step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25660step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw25660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25660step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw25660step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw25661step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw25661step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw25661step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw25662step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw25662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw25662step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw25699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw25704step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25704step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw25704step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25707step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw25708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw25709step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25709step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25709step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25713step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25713step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25735step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25737step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw25766step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25781step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw25781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw25791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25792step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw25792step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25838step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw25841step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw25845step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw25854step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25859step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw25888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25888step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25889step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw25914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw25914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25921 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25921step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25924step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25925step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25945step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25946step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25961step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25966step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25971step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25971step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw25972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25972step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25975step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25975step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical203
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25988step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw25988step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw26000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26065step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26069 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26080 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1], ![0, 0]]
def raw26080Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26080step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 0, 0], ![2, -1, -1]]
def raw26089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26091 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![0, 0], ![1, -1]]
def raw26091Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26091step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26098 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2], ![0, 0]]
def raw26098Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26109step1Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw26128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw26130Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw26132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw26134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26136step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26137step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26165 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26165step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw26167step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw26183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26185 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw26185Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26214step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26215step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26216step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26217step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26223step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26253step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26259step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26260step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26260step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw26262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26262step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26262step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26264step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26264step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26265step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26265step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26267step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw26267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26267step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26268step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26268step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26269step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26269step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw26272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw26273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26280 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw26280Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26280step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26280step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26281step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26282 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26282step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26282step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26283 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26283step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26283step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26284step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26284step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26285 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26285step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26286 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26286step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26287step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26287step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26288 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26288step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26288step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26288step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26290step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26290step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26290step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26290step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26291 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26291step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26291step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw26292step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26292step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26354step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26354step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26355step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26355step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26355step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26355step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26356step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26356step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26357step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26357step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26358step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26358step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26359step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![2, -2]]
def raw26360step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26360step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw26360step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26361step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw26361step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26361step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw26361step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26362step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw26362step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26362step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw26362step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw26363step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw26364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26365 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26366 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26367 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26370 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw26370Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26370step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw26370step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26370step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26370step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw26371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26380 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26381 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26393 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw26393Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26393step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw26393step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26393step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw26393step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26394 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26395 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26396 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw26396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26397 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -3, 2]]
def raw26413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2]]
def raw26414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26415 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![-2, 2]]
def raw26415Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26415step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26415step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26416 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 1, -2]]
def raw26424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26432 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]
def raw26432Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26432step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw26432step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26432step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw26432step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26433 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26434 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26435 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26436 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26437 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26438 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -2, 1]]
def raw26439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw26439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -3, 1]]
def raw26440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw26459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26463step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26464step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26465step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26466step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26467step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26470step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26472step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26472step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26474step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26496step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26497step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26498step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26501step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26501step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26502step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26503step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26503step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26504step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26506step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26507step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26508step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26509step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26511step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26511step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26512step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26514step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26514step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26516step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26517step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26518step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26520step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26550step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26551step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26553step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26553step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26554step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26555step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26555step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26555step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26556step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26557step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26557step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26558step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26559step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26559step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26562step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26563step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26563step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26563step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26564step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26565step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26565step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26565step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26566step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26566step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw26567step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26567step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26567step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26568step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw26568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26568step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26568step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw26569step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw26569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26570step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw26575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26581 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26581step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26586 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26586step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26591 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26591step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26596step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26597step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26598 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26598step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26599 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26599step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26600 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26600step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26607 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26608 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26609 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26610 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26611 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26612 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26615 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26622 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26623 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26627 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26630 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26633step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26645step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26646step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26649step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26649step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26650step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26653step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26654step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26656step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26657step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26679 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26679step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26680 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26681 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26682 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26682step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26683step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26684 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26684step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26685 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26685step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26686 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26686step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26688 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26688step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26689 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26689step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26690 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26690step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26691step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26692step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26694step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26695step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26696step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26697step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26698step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw26699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26699step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26700 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26700step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26707 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw26707Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26707step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26707step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26711step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26712step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26714step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26716step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26721step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26726step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26731step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26733step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


