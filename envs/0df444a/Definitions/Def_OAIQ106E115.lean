-- Prove2me | Definitions.Def_OAIQ106E115
-- name    : OAIQ106E115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:23:27.265043+00:00
-- url     : https://prove2.me/theorems/938f4c1a-fe53-4205-810e-e74e4e4774a2
-- title:
--   Definitions bundle OAIQ106E115 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7686 declarations of OpenAI's Lean: 7686 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw471step0`, `OAI.MUB6.Certificate.MixedSemantics.raw471step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw471step1`, `OAI.MUB6.Certificate.MixedSemantics.raw471step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw472`, `OAI.MUB6.Certificate.MixedSemantics.raw4720`, `OAI.MUB6.Certificate.MixedSemantics.raw4720Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step0`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step1`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step2`, `OAI.MUB6.Certificate.MixedSemantics.raw4720step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4721`, `OAI.MUB6.Certificate.MixedSemantics.raw4721Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step0`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step1`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step2`, `OAI.MUB6.Certificate.MixedSemantics.raw4721step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4722`, `OAI.MUB6.Certificate.MixedSemantics.raw4722Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step0`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step1`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step2`, `OAI.MUB6.Certificate.MixedSemantics.raw4722step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723`, `OAI.MUB6.Certificate.MixedSemantics.raw4723Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step0`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step1`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step2`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step3`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4723step4` and 7646 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical3`, `MutuallyUnbiased_MixedSemantics_Canonical36`, `MutuallyUnbiased_MixedSemantics_Canonical37`, `MutuallyUnbiased_MixedSemantics_Canonical38`, `MutuallyUnbiased_MixedSemantics_Canonical39`, `MutuallyUnbiased_MixedSemantics_Canonical4`, `MutuallyUnbiased_MixedSemantics_Canonical40`, `MutuallyUnbiased_MixedSemantics_Canonical41`, `MutuallyUnbiased_MixedSemantics_Canonical42`, `MutuallyUnbiased_MixedSemantics_Canonical43`, `MutuallyUnbiased_MixedSemantics_Canonical44`, `MutuallyUnbiased_MixedSemantics_Canonical45`, `MutuallyUnbiased_MixedSemantics_Canonical46`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1265_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1266_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1267_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3223_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3226_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3227_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3711_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3727_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3735_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3737_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3739_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3818_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3821_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3823_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3829_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3830_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3847_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3851_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3852_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3853_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3882_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3925_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3936_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3937_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3938_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3965_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3966_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3967_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3969_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3970_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3977_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5387_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5415_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5418_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5439_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5450_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5452_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5464_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5465_e`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound64_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound69_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound163_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound184_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound688_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound712_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound732_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound751_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound758_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound759_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound769_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound779_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound797_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound798_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound801_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound804_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound805_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound823_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound841_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound842_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound852_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound857_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound866_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound868_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound883_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound885_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound894_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound987_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`.
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

def raw4Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

def raw50 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4]]
def raw50Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw50step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw50step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw50step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw50step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw51 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4]]
def raw51Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw51step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw51step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw51step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw51step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw52 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw52Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw52step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw52step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw52step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw52step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw53 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw53Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw53step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw53step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw54 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw54Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw54step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw54step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw54step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw54step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw55 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw55Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw55step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw55step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw56 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw56Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw56step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw56step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw56step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw56step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw57 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw57Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw57step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw57step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw58 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw58Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw58step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw58step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw58step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw58step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw59 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw471step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw471step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw472 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw473 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw473step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw474 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw474step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw475step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw475step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw477step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw478 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw479step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw481step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw481step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw483 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw483Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw483step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw484 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw485Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw485step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw486 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw487 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw487Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw487step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw487step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw488 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw489 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw489Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw489step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw490 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw491Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw491step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw492 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw493 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw493Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw493step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw494 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw495 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw495Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw495step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw496 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw497 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw497Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw497step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw498 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw499 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw499Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw499step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw500 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw500step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw501 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw501Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw501step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw501step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw502 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw502step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw503 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw503step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw503step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw505 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw505step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw505step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw506 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw507 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw507step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw509step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw511Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw511step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw511step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw4733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw4743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4744 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw4744step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw4744step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw4749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw4753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4765step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4767step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4770step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4773step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4775 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4776 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw4776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4777 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw4780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4782 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4791 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4796 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4799step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4805step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4835step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4835step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4835step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4835step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4839step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw4839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4842step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw4842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4843step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw4843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4847step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw4847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4848step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4859step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4860step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw4860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4863step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw4863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4864step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4865step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4868step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4869step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4869step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4869step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4871step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4872step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4873step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4874step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw4874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4874step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4874step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4874step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4877step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw4877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw4877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4878step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw4878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4878step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4878step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw4878step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4879step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw4880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4881step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4883step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4883step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4883step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4883step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4884step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4884step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw4885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4885step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4885step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4889step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw4889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4889step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4889step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4889step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4890step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4890step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4890step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw4892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw4893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4893step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4893step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4893step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4893step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4893step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4894step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4894step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4894step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4894step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4894step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4895step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4895step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4895step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4895step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -2, -2]]
def raw4898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![4, -2, -2]]
def raw4898step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4898step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4898step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4898step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4900step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4903step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4903step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw4904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4905 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]
def raw4905Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw4905step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw4905step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4905step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw4905step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw4910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -2, -2]]
def raw4918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![4, -2, -2]]
def raw4918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4918step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4923step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4924step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4924step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4924step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4924step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4925step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4925step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw4926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4926step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4926step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4928step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4928step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4931step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4932step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4932step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4934step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4935step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4935step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4935step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4936step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4936step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4940step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4940step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4940step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4940step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4941step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4942step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4942step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4942step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![4, -3, -1]]
def raw4943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw4943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4943step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4943step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4944step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw4944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw4948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw4948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4957step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw4958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw4961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw4962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![4, -3, -1]]
def raw4965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw4965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4966 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw4966step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4966step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4966step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4966step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4966step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4966step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4966step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4967 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4967step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4967step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4968 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4968step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4968step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4969step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4969step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4969step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4969step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4969step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4970step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4970step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4970step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw4971step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4971step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4971step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4972 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4972step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4972step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4972step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4973step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4973step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4974step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4974step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4974step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4975step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4976 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4976step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4976step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4976step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4976step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4977step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4977step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4978 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4978step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4979step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4980 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4980step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4981 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4981step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4981step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4982step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4982step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4982step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4983 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4984 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4985 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4986step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4986step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4986step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4988step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4988step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4988step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw4989step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw4989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw4990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4990step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4990step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4990step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4990step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4990step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4990step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4991 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4992 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4992step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4993step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4994 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4994step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4994step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4995 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4996 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4997 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4998 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5002 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw5002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5003 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5009 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5009step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5011 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5013 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5013step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5014step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5015 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5015step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5016step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5016step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw5017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5018step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5018step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw5021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw5021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5022 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5022step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5022step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5022step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5023 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5023step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5024 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5025 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5025step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5026 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5027 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-3, 3, 0]]
def raw5027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5027step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5027step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5027step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5029step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw5030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw5030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw5031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5031step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5031step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5031step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5035step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5035step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5035step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5042 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5042step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw5042step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5042step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5042step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5042step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5042step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw5043step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw5043step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5043step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw5043step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5044step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5044step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5045step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5045step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw5046step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5046step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5046step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5046step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5046step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5046step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5047 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw5047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw5047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5048step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5048step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5048step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5051step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw5053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw5056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw5056step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5058step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5059step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5060step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5060step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5061step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5061step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![2, 0, -2]]
def raw5062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2]]
def raw5062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw5062step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5062step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw5062step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![4, -2, -2]]
def raw5083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw5083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5084step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5085step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5086step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5086step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5087step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5087step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5088step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5088step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5088step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5088step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5088step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5089step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5089step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5089step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5089step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5089step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5090step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5090step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5090step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5090step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5090step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5091step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5091step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5092step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5092step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5092step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5093step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5094step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5094step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5095step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5095step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5095step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5096step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5096step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -3, 3]]
def raw5097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 3, -3], ![0, -3, 3]]
def raw5097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -3], ![-3, 3]]
def raw5097step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw5097step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw5097step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw5097step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw5097step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5098step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5098step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5098step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5098step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5098step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5099step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5099step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5099step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5099step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5099step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5100step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5100step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5100step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5100step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5100step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5102step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5104step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5104step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5104step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5104step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw5105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5105step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5105step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5105step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5111step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5119step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw513Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw513step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw513step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw514 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw515 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw515Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw515step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw516 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw517Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw517step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw519 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw519Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw519step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw519step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw520 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw521 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw521Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw521step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw521step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw523Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw523step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw523step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw525Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw525step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw526 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw527 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw527Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw527step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw528 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw529 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw529Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw529step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw529step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw531 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw531Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw531step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw532 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw533 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw533Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw533step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw533step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw534 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw535 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw535Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw535step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw536 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw537 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw537Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw537step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw538 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw539 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw539Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw539step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw540 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw541 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw541Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw541step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw541step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw542 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw543 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw543Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw543step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw544 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1]]
def raw544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw545 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1]]
def raw545Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw545step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw546 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2]]
def raw546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw547 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2]]
def raw547Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw547step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw547step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw548 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw549 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw549Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw549step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw549step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw550 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw551 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw551Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw551step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw551step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw551step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw552 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1]]
def raw552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw553 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1]]
def raw553Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw553step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw554 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 2, -2]]
def raw554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw554step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw554step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw555 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 2, -2]]
def raw555Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw555step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw555step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw559Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw559step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw559step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw560 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw561 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw561Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw561step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw561step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw563Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw563step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw564 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw565 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw565Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw565step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw568 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw569 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw569Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw569step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw569step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw570 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw571 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw571Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw571step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw571step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw573Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw573step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw575Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw575step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw577Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw577step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw578 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw579 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw579Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw579step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw581Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw581step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw582Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw583Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw583step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw583step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw585Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw585step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw585step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw587Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw587step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw589Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw589step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw589step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5120step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5122step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5124step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5125step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw5126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5126step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw5126step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw5130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw5130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5130step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw5130step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5131step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5131step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5132step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw5134step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5134step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5134step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5134step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5134step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5134step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5134step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5135step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw5135step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5135step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5135step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5135step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5135step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5136step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5136step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5139step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5140step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5140step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5141step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5141step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5141step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5144step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5145step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5146step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5149step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5150step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5150step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5151step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5151step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5151step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw5151step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5151step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw5151step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5152step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5152step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5152step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5153step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5153step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5154step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5154step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5154step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5155step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5155step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5155step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5155step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5156step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5156step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5156step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw5156step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5156step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw5156step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5157step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5157step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5157step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5158step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5158step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5159step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw5160step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5160step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw5160step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5160step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw5160step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw5161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5161step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5161step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5165step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw5165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw5166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw5166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5166step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw5166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5167 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw5167step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5167step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5167step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5167step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5167step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw5176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw5178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5178step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw5179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5179step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw5179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5180 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5180step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5180step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5180step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5180step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5180step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5181step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5181step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5181step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5181step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5182step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5182step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5182step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5182step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -3, 3]]
def raw5183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5183step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw5183step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5183step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw5183step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5183step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw5183step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5184step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5187step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5188step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5188step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5191step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -4, 3]]
def raw5192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5192step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw5192step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5192step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw5192step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5193step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5193step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5194step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -4, 3]]
def raw5195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5195step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -4, 3]]
def raw5196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5196step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw5196step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5196step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw5196step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5197step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5197step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5197step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5197step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5198step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5198step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5198step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5198step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5198step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5199step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5199step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5199step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5199step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5199step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5200step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5200step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5200step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5200step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5200step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5201Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5201step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5201step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5201step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5201step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5201step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5202Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5202step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5202step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5202step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5202step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5203Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5203step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5203step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5203step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5203step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5203step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5203step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5204step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5204step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5204step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5204step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5204step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5205Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5205step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5205step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5205step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5206Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5206step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5206step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5206step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5206step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw5207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5207step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5207step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5207step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5207step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw5208step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5208step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw5208step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5208step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5208step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5209step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5209step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5209step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5210step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5210step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5210step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5211step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5211step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5211step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw5212step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5212step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw5212step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5213step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 4, 0], ![4, -4, 0]]
def raw5213step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5213step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw5213step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5214step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5214step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5214step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5214step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5214step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5214step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5214step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5214step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5215step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5215step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5215step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5215step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5215step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5215step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5215step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5215step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw5216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5216step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5216step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5216step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5216step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5216step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5216step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5216step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw5217step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5217step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw5217step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5217step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw5217step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5217step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw5217step5Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw5249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw5250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5251step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw5251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5266step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw5266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5266step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw5266step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw5270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw5273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw5275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw5275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw5276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw5276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw5277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw5277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5314 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]
def raw5314Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw5314step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw5314step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5314step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw5382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw5402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5405 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw5405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5405step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw5405step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw5408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 3, 0]]
def raw5418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw5420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw5421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw5426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5431step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5431step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5431step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5460step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw5486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5491step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5503step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5523 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]
def raw5523Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5523step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw5523step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5523step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw5523step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5543step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5544step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5544step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5544step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5551step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5556step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5561step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5566step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw5574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw5594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5601step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw5634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5636 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw5636Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw5636step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw5636step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5636step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw5636step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw5657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw5657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5659step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5661step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5664step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5664step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5664step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5669step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5669step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5670step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5670step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5670step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5674step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5675step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5678step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5678step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5679step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5681step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5682step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5683step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5683step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5683step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5684step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5685step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5687step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5687step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw5691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw5692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw5712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw5717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5723step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5732step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw5741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5746 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5747step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw5751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5752 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw5752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5753 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5754 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-1, 1], ![-2, 2]]
def raw5754step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5754step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5754step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5754step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5760 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw5762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw5763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw5767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw5770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5771step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5797step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5797step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5797step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5797step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5831step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5832step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5833step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5834step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5834step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5834step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5835step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw5835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw5835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5836step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5836step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw5836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5836step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw5836step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw5838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5839step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw5839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw5839step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5839step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw5839step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5840step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5841step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5843step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5844step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5844step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5846step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw5846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5847step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5849step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw5849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5849step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5849step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5849step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5851step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5851step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw5851step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw5851step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5852step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw5852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5852step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw5852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw5854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5856step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5856step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw5856step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5856step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw5856step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5857step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5857step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw5859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5860step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw5862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw5866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw5866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5867 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw5867Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw5867step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]
def raw5867step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5867step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5867step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5867step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5867step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw5874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 3, -3], ![2, -2, 0]]
def raw5875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5875step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 2, -3], ![1, -1, 0]]
def raw5876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw5879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![1, -1, 0]]
def raw5883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw5887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw5887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw5888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


