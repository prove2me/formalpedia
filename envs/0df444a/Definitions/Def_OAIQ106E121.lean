-- Prove2me | Definitions.Def_OAIQ106E121
-- name    : OAIQ106E121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T22:53:32.256195+00:00
-- url     : https://prove2.me/theorems/b0560661-3ac7-494c-81db-7d12bc721a46
-- title:
--   Definitions bundle OAIQ106E121 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 710 declarations of OpenAI's Lean: 710 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1976`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1978`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1980`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1981`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1982`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1983`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1984`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1985`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1986`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1987`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1988`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1989`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow199`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1990`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1991`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1992`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1993`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1994`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1995`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1996`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1997`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1998`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow1999`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow20`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2000`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2001`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2002`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2003`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2004`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2005`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2006`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2007`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2008`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2009`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2010`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2011`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2012`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2013`, `OAI.MUB6.Certificate.MixedSourceBridge.numericRow2014` and 670 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSources_Arithmetic0`, `MutuallyUnbiased_MixedSources_Arithmetic1`, `MutuallyUnbiased_MixedSources_Arithmetic12`, `MutuallyUnbiased_MixedSources_Arithmetic123`, `MutuallyUnbiased_MixedSources_Arithmetic124`, `MutuallyUnbiased_MixedSources_Arithmetic125`, `MutuallyUnbiased_MixedSources_Arithmetic126`, `MutuallyUnbiased_MixedSources_Arithmetic127`, `MutuallyUnbiased_MixedSources_Arithmetic128`, `MutuallyUnbiased_MixedSources_Arithmetic129`, `MutuallyUnbiased_MixedSources_Arithmetic13`, `MutuallyUnbiased_MixedSources_Arithmetic130`, `MutuallyUnbiased_MixedSources_Arithmetic131`, `MutuallyUnbiased_MixedSources_Arithmetic132`, `MutuallyUnbiased_MixedSources_Arithmetic133`, `MutuallyUnbiased_MixedSources_Arithmetic134`, `MutuallyUnbiased_MixedSources_Arithmetic135`, `MutuallyUnbiased_MixedSources_Arithmetic14`, `MutuallyUnbiased_MixedSources_Arithmetic15`, `MutuallyUnbiased_MixedSources_Arithmetic16`, `MutuallyUnbiased_MixedSources_Arithmetic17`, `MutuallyUnbiased_MixedSources_Arithmetic18`, `MutuallyUnbiased_MixedSources_Arithmetic19`, `MutuallyUnbiased_MixedSources_Arithmetic2`, `MutuallyUnbiased_MixedSources_Arithmetic20`, `MutuallyUnbiased_MixedSources_Arithmetic21`, `MutuallyUnbiased_MixedSources_Arithmetic22`, `MutuallyUnbiased_MixedSources_Arithmetic23`, `MutuallyUnbiased_MixedSources_Arithmetic24`, `MutuallyUnbiased_MixedSources_Arithmetic25`, `MutuallyUnbiased_MixedSources_Arithmetic26`, `MutuallyUnbiased_MixedSources_Arithmetic27`, `MutuallyUnbiased_MixedSources_Arithmetic28`, `MutuallyUnbiased_MixedSources_Arithmetic29`, `MutuallyUnbiased_MixedSources_Arithmetic3`, `MutuallyUnbiased_MixedSources_Arithmetic30`, `MutuallyUnbiased_MixedSources_Arithmetic31`, `MutuallyUnbiased_MixedSources_Arithmetic32`, `MutuallyUnbiased_MixedSources_Arithmetic33`, `MutuallyUnbiased_MixedSources_Arithmetic34`, `MutuallyUnbiased_MixedSources_Arithmetic35`, `MutuallyUnbiased_MixedSources_Arithmetic36`, `MutuallyUnbiased_MixedSources_Arithmetic37`, `MutuallyUnbiased_MixedSources_Arithmetic38`, `MutuallyUnbiased_MixedSources_Arithmetic39`, `MutuallyUnbiased_MixedSources_Arithmetic4`, `MutuallyUnbiased_MixedSources_Arithmetic40`, `MutuallyUnbiased_MixedSources_Arithmetic41`, `MutuallyUnbiased_MixedTargets_OriginalBlock1`, `MutuallyUnbiased_MixedTargets_ReductionMergeData31`.
--
--   **Imports.** It imports the bundle `OAIQ106E043` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E131`; the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1985_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2035_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2038_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2039_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2074_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2082_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2084_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2085_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2088_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2089_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2090_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2091_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound213_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound214_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound226_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound245_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound281_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound282_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound287_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound526_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound552_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound565_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound579_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound591_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound592_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound607_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound608_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound614_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound636_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound644_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound664_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2 : Integer.Sparse Master := [(Sum.inl 0, -35), (Sum.inl 12, -40), (Sum.inl 1, 75), (Sum.inr 2245, 720), (Sum.inr 2247, 360), (Sum.inr 2266, 720), (Sum.inr 3077, 720), (Sum.inr 3801, 720), (Sum.inr 3809, 1440), (Sum.inr 3910, 720), (Sum.inr 3913, 720)]

def numericRow3 : Integer.Sparse Master := [(Sum.inl 0, 26), (Sum.inl 12, 40), (Sum.inl 1, 150), (Sum.inr 3053, -720), (Sum.inr 3054, -720), (Sum.inr 3619, -720), (Sum.inr 3623, -360), (Sum.inr 3626, -720), (Sum.inr 3814, -1440), (Sum.inr 3899, -720), (Sum.inr 3902, -720)]

def numericRow4 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 2723, -16), (Sum.inr 2726, -4), (Sum.inr 2743, -8), (Sum.inr 3544, -16), (Sum.inr 3545, -4), (Sum.inr 3548, -8), (Sum.inr 3627, -8), (Sum.inr 3958, -16), (Sum.inr 3961, -16), (Sum.inr 3963, -8), (Sum.inr 4047, -16)]

def numericRow5 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 1, 1), (Sum.inr 2723, 24), (Sum.inr 2726, 6), (Sum.inr 2743, 12), (Sum.inr 3958, 24), (Sum.inr 3963, 6)]

def numericRow6 : Integer.Sparse Master := [(Sum.inl 0, 26), (Sum.inl 2, 20), (Sum.inl 3, 320), (Sum.inl 4, 320), (Sum.inl 1, 10), (Sum.inl 31, -480)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow20 : Integer.Sparse Master := [(Sum.inl 0, 220), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, -245), (Sum.inr 3849, -2160), (Sum.inr 3850, -2160), (Sum.inr 3857, -2160), (Sum.inr 3875, -2160), (Sum.inr 3876, -2160), (Sum.inr 3901, -2160), (Sum.inr 3903, -2160), (Sum.inr 3906, -2160), (Sum.inr 3910, -2160), (Sum.inr 3983, -2160)]

def numericRow21 : Integer.Sparse Master := [(Sum.inl 0, 23), (Sum.inl 4, -80), (Sum.inl 1, -15), (Sum.inr 2782, -720), (Sum.inr 2783, -240), (Sum.inr 3583, -720), (Sum.inr 3633, -240), (Sum.inr 3913, -720), (Sum.inr 3983, -1440)]

def numericRow22 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 1, 5), (Sum.inr 3622, -240), (Sum.inr 3623, -120), (Sum.inr 3627, -240), (Sum.inr 4010, -240), (Sum.inr 4046, -240), (Sum.inr 4047, -480)]

def numericRow23 : Integer.Sparse Master := [(Sum.inl 0, 174), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 160), (Sum.inl 1, -215), (Sum.inr 3910, -2160), (Sum.inr 3913, -2160), (Sum.inr 4010, -4320)]

def numericRow24 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3622, -16), (Sum.inr 3627, -8), (Sum.inr 3632, -8), (Sum.inr 3901, -16), (Sum.inr 3903, -16), (Sum.inr 3906, -16), (Sum.inr 3907, -8), (Sum.inr 3910, -16), (Sum.inr 3913, -8)]

def numericRow25 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 1, -5), (Sum.inr 4083, 120), (Sum.inr 4084, 80), (Sum.inr 4091, 240), (Sum.inr 4092, 240)]

def numericRow26 : Integer.Sparse Master := [(Sum.inl 0, 82), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, 40), (Sum.inl 4, -160), (Sum.inl 1, 155), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 4046, -4320)]

def numericRow27 : Integer.Sparse Master := [(Sum.inl 0, 76), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 95), (Sum.inr 3837, -540), (Sum.inr 3838, -1080), (Sum.inr 3843, -1080), (Sum.inr 3901, -1080), (Sum.inr 3974, -1080), (Sum.inr 4046, -1080)]

def numericRow28 : Integer.Sparse Master := [(Sum.inl 0, 468), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -160), (Sum.inl 1, 425), (Sum.inr 3901, -2160), (Sum.inr 3902, -2160), (Sum.inr 3903, -4320), (Sum.inr 4010, -2160), (Sum.inr 4046, -6480), (Sum.inr 4047, -4320)]

def numericRow29 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 1, 5), (Sum.inr 4091, 720), (Sum.inr 4092, 360)]

def numericRow30 : Integer.Sparse Master := [(Sum.inr 1092, 1), (Sum.inr 2063, 3), (Sum.inr 2285, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def numericRow31 : Integer.Sparse Master := [(Sum.inr 1067, 3), (Sum.inr 1069, 1), (Sum.inr 1092, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow199 : Integer.Sparse Master := [(Sum.inl 0, -56), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 12, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -80), (Sum.inr 1184, 8640), (Sum.inr 1186, 4320), (Sum.inr 1192, 4320), (Sum.inr 1292, 4320), (Sum.inr 1610, 8640), (Sum.inr 1628, 4320), (Sum.inr 1716, 4320), (Sum.inr 2837, 8640), (Sum.inr 2842, 4320), (Sum.inr 2906, 8640), (Sum.inr 2910, 8640), (Sum.inr 2952, 8640), (Sum.inr 3024, 8640), (Sum.inr 3051, 8640), (Sum.inr 3055, 4320), (Sum.inr 3098, 4320), (Sum.inr 3541, 8640), (Sum.inr 3549, 4320), (Sum.inr 3626, 4320)]

def numericRow202 : Integer.Sparse Master := [(Sum.inr 1436, 1), (Sum.inr 2759, 2), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def numericRow203 : Integer.Sparse Master := [(Sum.inr 1283, 1), (Sum.inr 2582, 2), (Sum.inr 2651, 1), (Sum.inr 2774, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def numericRow204 : Integer.Sparse Master := [(Sum.inr 1422, 1), (Sum.inr 2580, 1), (Sum.inr 2582, 1), (Sum.inr 2600, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def numericRow205 : Integer.Sparse Master := [(Sum.inr 1280, 1), (Sum.inr 2580, 1), (Sum.inr 2647, 1), (Sum.inr 2759, 1), (Sum.inr 2773, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def numericRow206 : Integer.Sparse Master := [(Sum.inr 1280, 2), (Sum.inr 1282, 1), (Sum.inr 1283, 1), (Sum.inr 1306, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def numericRow207 : Integer.Sparse Master := [(Sum.inl 0, -244), (Sum.inl 6, -20), (Sum.inl 2, 120), (Sum.inl 3, -640), (Sum.inl 13, -640), (Sum.inl 52, 320), (Sum.inr 1060, 17280), (Sum.inr 1061, 8640), (Sum.inr 1062, 8640), (Sum.inr 1088, 8640), (Sum.inr 2496, 17280), (Sum.inr 2497, 17280), (Sum.inr 2498, 17280), (Sum.inr 2516, 17280), (Sum.inr 2641, 17280), (Sum.inr 2643, 8640), (Sum.inr 2748, 17280), (Sum.inr 2761, 8640), (Sum.inr 2765, 8640), (Sum.inr 2771, 8640), (Sum.inr 2777, 17280), (Sum.inr 2789, 8640), (Sum.inr 3086, 17280)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1976 : Integer.Sparse Master := [(Sum.inl 0, 192), (Sum.inl 5, 60), (Sum.inl 2, -60), (Sum.inl 7, 240), (Sum.inl 3, 960), (Sum.inl 23, -720), (Sum.inl 12, 480), (Sum.inl 4, 480), (Sum.inl 27, -180), (Sum.inl 1, 60), (Sum.inr 730, -12960), (Sum.inr 731, -12960), (Sum.inr 734, -25920), (Sum.inr 780, -12960), (Sum.inr 781, -12960), (Sum.inr 789, -12960), (Sum.inr 800, -25920), (Sum.inr 823, -12960), (Sum.inr 1802, -12960), (Sum.inr 1804, -12960), (Sum.inr 1810, -25920), (Sum.inr 1874, -12960), (Sum.inr 1876, -25920), (Sum.inr 1896, -12960), (Sum.inr 1900, -12960), (Sum.inr 1906, -25920), (Sum.inr 1921, -12960), (Sum.inr 2016, -25920), (Sum.inr 2018, -51840), (Sum.inr 2028, -25920), (Sum.inr 2048, -25920), (Sum.inr 2075, -25920), (Sum.inr 2082, -25920), (Sum.inr 2105, -12960), (Sum.inr 2107, -25920), (Sum.inr 2141, -12960), (Sum.inr 2143, -12960), (Sum.inr 2152, -25920), (Sum.inr 2215, -25920), (Sum.inr 2241, -12960), (Sum.inr 2245, -12960), (Sum.inr 2260, -25920), (Sum.inr 2277, -12960), (Sum.inr 3786, -12960), (Sum.inr 3799, -12960), (Sum.inr 3850, -51840), (Sum.inr 3891, -12960), (Sum.inr 3910, -12960)]

def numericRow1978 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 190), (Sum.inr 1035, -8640), (Sum.inr 1645, -8640), (Sum.inr 2016, -8640), (Sum.inr 2019, -4320), (Sum.inr 2052, -4320), (Sum.inr 2075, -8640), (Sum.inr 2101, -17280), (Sum.inr 2107, -8640), (Sum.inr 2190, -4320), (Sum.inr 2193, -4320), (Sum.inr 2260, -8640), (Sum.inr 2884, -4320), (Sum.inr 3603, -4320), (Sum.inr 3621, -4320), (Sum.inr 4435, 17280), (Sum.inr 4437, 17280), (Sum.inr 4443, 17280), (Sum.inr 4791, 17280), (Sum.inr 4794, 17280), (Sum.inr 4848, 34560), (Sum.inr 4850, 34560), (Sum.inr 4851, 17280), (Sum.inr 4855, 34560), (Sum.inr 4879, 17280), (Sum.inr 5184, 17280), (Sum.inr 5198, 34560)]

def numericRow1980 : Integer.Sparse Master := [(Sum.inr 929, -1), (Sum.inr 1044, -1), (Sum.inr 1680, -1), (Sum.inr 1737, -1), (Sum.inr 1811, -1), (Sum.inr 2020, -2), (Sum.inr 2023, -2), (Sum.inr 2110, -1), (Sum.inr 2156, -1), (Sum.inr 2202, -2), (Sum.inr 2214, -2), (Sum.inr 2245, -2), (Sum.inr 2275, -1), (Sum.inr 2277, -2), (Sum.inr 2721, -1), (Sum.inr 3532, -1), (Sum.inr 4331, 4), (Sum.inr 4332, 8), (Sum.inr 4667, 4), (Sum.inr 4668, 8), (Sum.inr 4765, 4), (Sum.inr 4775, 8), (Sum.inr 4793, 8), (Sum.inr 4795, 8), (Sum.inr 5231, 4), (Sum.inr 5263, 4), (Sum.inr 5265, 8)]

def numericRow1981 : Integer.Sparse Master := [(Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1737, 1), (Sum.inr 2154, 2), (Sum.inr 2156, 1), (Sum.inr 2160, 1), (Sum.inr 2179, 1), (Sum.inr 2202, 2), (Sum.inr 2211, 2), (Sum.inr 2213, 2), (Sum.inr 2214, 2), (Sum.inr 2219, 2), (Sum.inr 2275, 1), (Sum.inr 2277, 2), (Sum.inr 2676, 1), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2730, 2)]

def numericRow1982 : Integer.Sparse Master := [(Sum.inr 1793, 1), (Sum.inr 1794, 2), (Sum.inr 1811, 1), (Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 4083, -1)]

def numericRow1983 : Integer.Sparse Master := [(Sum.inl 0, 339), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -120), (Sum.inl 7, -480), (Sum.inl 3, -960), (Sum.inl 23, 720), (Sum.inl 12, -240), (Sum.inl 27, 180), (Sum.inl 1, -690), (Sum.inr 702, -12960), (Sum.inr 703, -25920), (Sum.inr 719, -12960), (Sum.inr 754, -25920), (Sum.inr 756, -12960), (Sum.inr 760, -12960), (Sum.inr 786, -12960), (Sum.inr 822, -12960), (Sum.inr 1762, -12960), (Sum.inr 1763, -25920), (Sum.inr 1776, -12960), (Sum.inr 1842, -25920), (Sum.inr 1844, -12960), (Sum.inr 1847, -12960), (Sum.inr 1964, -12960), (Sum.inr 1966, -25920), (Sum.inr 2016, -25920), (Sum.inr 2023, -12960), (Sum.inr 2025, -25920), (Sum.inr 2028, -25920), (Sum.inr 2046, -12960), (Sum.inr 2058, -25920), (Sum.inr 2075, -25920), (Sum.inr 2077, -12960), (Sum.inr 2105, -12960), (Sum.inr 2177, -25920), (Sum.inr 2182, -12960), (Sum.inr 2214, -12960), (Sum.inr 2215, -25920), (Sum.inr 2216, -25920), (Sum.inr 2224, -25920), (Sum.inr 2241, -12960), (Sum.inr 2245, -25920), (Sum.inr 2277, -25920), (Sum.inr 3692, -12960), (Sum.inr 3769, -12960), (Sum.inr 3849, -12960), (Sum.inr 3875, -12960), (Sum.inr 3897, -12960), (Sum.inr 3906, -25920)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow1984 : Integer.Sparse Master := [(Sum.inr 922, -1), (Sum.inr 1041, -1), (Sum.inr 1673, -1), (Sum.inr 1724, -1), (Sum.inr 1805, -1), (Sum.inr 2020, -2), (Sum.inr 2023, -1), (Sum.inr 2025, -1), (Sum.inr 2029, -1), (Sum.inr 2107, -1), (Sum.inr 2150, -1), (Sum.inr 2202, -2), (Sum.inr 2214, -1), (Sum.inr 2224, -1), (Sum.inr 2225, -1), (Sum.inr 2244, -1), (Sum.inr 2260, -1), (Sum.inr 2262, -1), (Sum.inr 2721, -1), (Sum.inr 2739, -1), (Sum.inr 3532, -1), (Sum.inr 3534, -1), (Sum.inr 4327, 4), (Sum.inr 4332, 4), (Sum.inr 4664, 4), (Sum.inr 4666, 4), (Sum.inr 4668, 4), (Sum.inr 4772, 4), (Sum.inr 4774, 4), (Sum.inr 4775, 4), (Sum.inr 4792, 4), (Sum.inr 4795, 4), (Sum.inr 5226, 4), (Sum.inr 5255, 4)]

def numericRow1985 : Integer.Sparse Master := [(Sum.inl 0, -374), (Sum.inl 9, 100), (Sum.inl 58, -5), (Sum.inl 5, -200), (Sum.inl 6, 30), (Sum.inl 68, -300), (Sum.inl 2, -245), (Sum.inl 69, 80), (Sum.inl 70, 80), (Sum.inl 71, 320), (Sum.inl 7, 240), (Sum.inl 35, 480), (Sum.inl 8, 320), (Sum.inl 125, -240), (Sum.inl 3, 1440), (Sum.inl 13, 800), (Sum.inl 52, 320), (Sum.inl 197, -960), (Sum.inl 54, -240), (Sum.inl 24, -480), (Sum.inl 55, -240), (Sum.inl 12, 320), (Sum.inl 56, -480), (Sum.inl 26, 320), (Sum.inl 4, 320), (Sum.inl 27, -180), (Sum.inl 1, -710), (Sum.inr 1327, 4320), (Sum.inr 1328, 4320), (Sum.inr 2423, 4320), (Sum.inr 2430, 4320), (Sum.inr 2471, 4320), (Sum.inr 3084, 4320), (Sum.inr 3091, 4320), (Sum.inr 3133, 4320), (Sum.inr 3135, 4320), (Sum.inr 3162, 4320), (Sum.inr 3164, 4320), (Sum.inr 3199, 4320)]

def numericRow1986 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1724, 1), (Sum.inr 2147, 1), (Sum.inr 2148, 1), (Sum.inr 2150, 1), (Sum.inr 2154, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2211, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 1), (Sum.inr 2224, 1), (Sum.inr 2225, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2669, 1), (Sum.inr 2718, 1), (Sum.inr 2721, 1), (Sum.inr 2739, 1)]

def numericRow1987 : Integer.Sparse Master := [(Sum.inr 1790, 1), (Sum.inr 1792, 1), (Sum.inr 1794, 1), (Sum.inr 1805, 1), (Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 4083, -1)]

def numericRow1988 : Integer.Sparse Master := [(Sum.inl 0, 369), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -195), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -1200), (Sum.inl 24, 720), (Sum.inl 12, -480), (Sum.inl 4, -720), (Sum.inl 27, 180), (Sum.inl 1, 105), (Sum.inr 699, -12960), (Sum.inr 700, -12960), (Sum.inr 704, -12960), (Sum.inr 713, -12960), (Sum.inr 748, -12960), (Sum.inr 749, -12960), (Sum.inr 751, -12960), (Sum.inr 761, -12960), (Sum.inr 783, -12960), (Sum.inr 803, -12960), (Sum.inr 1760, -12960), (Sum.inr 1761, -12960), (Sum.inr 1764, -12960), (Sum.inr 1771, -12960), (Sum.inr 1836, -12960), (Sum.inr 1837, -12960), (Sum.inr 1838, -12960), (Sum.inr 1848, -12960), (Sum.inr 1960, -12960), (Sum.inr 1963, -12960), (Sum.inr 1967, -12960), (Sum.inr 1987, -12960), (Sum.inr 1990, -12960), (Sum.inr 1996, -12960), (Sum.inr 1997, -12960), (Sum.inr 2000, -25920), (Sum.inr 2019, -12960), (Sum.inr 2020, -25920), (Sum.inr 2022, -12960), (Sum.inr 2029, -12960), (Sum.inr 2051, -25920), (Sum.inr 2054, -12960), (Sum.inr 2173, -12960), (Sum.inr 2174, -12960), (Sum.inr 2183, -12960), (Sum.inr 2190, -12960), (Sum.inr 2191, -25920), (Sum.inr 2202, -25920), (Sum.inr 2203, -12960), (Sum.inr 2206, -12960), (Sum.inr 2225, -12960), (Sum.inr 2243, -25920), (Sum.inr 2244, -12960), (Sum.inr 2262, -12960), (Sum.inr 3690, -12960), (Sum.inr 3764, -12960), (Sum.inr 3838, -12960), (Sum.inr 3843, -12960), (Sum.inr 3896, -12960), (Sum.inr 3901, -12960), (Sum.inr 3903, -12960)]

def numericRow1989 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -20), (Sum.inr 977, -4320), (Sum.inr 998, -4320), (Sum.inr 1597, -4320), (Sum.inr 1600, -4320), (Sum.inr 1909, -8640), (Sum.inr 1913, -4320), (Sum.inr 1922, -4320), (Sum.inr 2016, -4320), (Sum.inr 2019, -4320), (Sum.inr 2020, -4320), (Sum.inr 2023, -4320), (Sum.inr 2054, -4320), (Sum.inr 2075, -4320), (Sum.inr 2107, -4320), (Sum.inr 2190, -4320), (Sum.inr 2202, -4320), (Sum.inr 2206, -4320), (Sum.inr 2214, -4320), (Sum.inr 2260, -4320), (Sum.inr 2480, -4320), (Sum.inr 2924, -4320), (Sum.inr 3467, -4320), (Sum.inr 3605, -4320), (Sum.inr 3607, -4320), (Sum.inr 4400, 17280), (Sum.inr 4449, 17280), (Sum.inr 4799, 17280), (Sum.inr 4803, 17280), (Sum.inr 4813, 17280), (Sum.inr 4815, 17280), (Sum.inr 4816, 17280), (Sum.inr 4849, 17280), (Sum.inr 4851, 17280), (Sum.inr 4852, 17280), (Sum.inr 5145, 17280)]

def numericRow1990 : Integer.Sparse Master := [(Sum.inr 919, -1), (Sum.inr 1040, -1), (Sum.inr 1664, -1), (Sum.inr 1707, -1), (Sum.inr 1802, -1), (Sum.inr 2022, -2), (Sum.inr 2028, -2), (Sum.inr 2051, -1), (Sum.inr 2106, -1), (Sum.inr 2141, -1), (Sum.inr 2191, -1), (Sum.inr 2203, -2), (Sum.inr 2215, -2), (Sum.inr 2242, -1), (Sum.inr 2244, -1), (Sum.inr 2262, -1), (Sum.inr 2722, -2), (Sum.inr 3533, -2), (Sum.inr 4328, 8), (Sum.inr 4663, 4), (Sum.inr 4665, 8), (Sum.inr 4771, 4), (Sum.inr 4773, 8), (Sum.inr 4803, 8), (Sum.inr 5219, 4), (Sum.inr 5249, 4)]

def numericRow1991 : Integer.Sparse Master := [(Sum.inl 0, -420), (Sum.inl 9, 100), (Sum.inl 58, -5), (Sum.inl 5, 260), (Sum.inl 6, -65), (Sum.inl 68, -300), (Sum.inl 2, 475), (Sum.inl 69, 160), (Sum.inl 70, 160), (Sum.inl 71, 160), (Sum.inl 125, -480), (Sum.inl 3, 160), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 196, -240), (Sum.inl 197, -480), (Sum.inl 23, -240), (Sum.inl 54, 480), (Sum.inl 55, -480), (Sum.inl 12, 160), (Sum.inl 26, -320), (Sum.inl 27, -180), (Sum.inl 1, 555), (Sum.inr 1330, 8640), (Sum.inr 2890, 4320), (Sum.inr 2895, 4320), (Sum.inr 3066, 4320), (Sum.inr 3069, 4320), (Sum.inr 3134, 8640), (Sum.inr 3163, 8640), (Sum.inr 3202, 8640)]

def numericRow1992 : Integer.Sparse Master := [(Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1707, 1), (Sum.inr 2140, 1), (Sum.inr 2141, 1), (Sum.inr 2144, 2), (Sum.inr 2189, 1), (Sum.inr 2191, 1), (Sum.inr 2194, 2), (Sum.inr 2195, 2), (Sum.inr 2203, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 2722, 2)]

def numericRow1993 : Integer.Sparse Master := [(Sum.inl 0, 216), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -75), (Sum.inl 7, -480), (Sum.inl 3, -1680), (Sum.inl 23, 720), (Sum.inl 12, -960), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, 930), (Sum.inr 698, -12960), (Sum.inr 700, -25920), (Sum.inr 710, -12960), (Sum.inr 744, -12960), (Sum.inr 746, -12960), (Sum.inr 749, -25920), (Sum.inr 782, -25920), (Sum.inr 1759, -12960), (Sum.inr 1761, -25920), (Sum.inr 1769, -12960), (Sum.inr 1833, -12960), (Sum.inr 1835, -12960), (Sum.inr 1837, -25920), (Sum.inr 1959, -12960), (Sum.inr 1963, -25920), (Sum.inr 1986, -51840), (Sum.inr 1990, -51840), (Sum.inr 1997, -51840), (Sum.inr 2019, -38880), (Sum.inr 2020, -25920), (Sum.inr 2051, -12960), (Sum.inr 2170, -12960), (Sum.inr 2174, -25920), (Sum.inr 2190, -38880), (Sum.inr 2191, -12960), (Sum.inr 2202, -25920), (Sum.inr 2243, -25920), (Sum.inr 3689, -12960), (Sum.inr 3757, -12960), (Sum.inr 3837, -51840), (Sum.inr 3895, -12960), (Sum.inr 3901, -12960)]

def numericRow1994 : Integer.Sparse Master := [(Sum.inl 0, 38), (Sum.inl 6, -5), (Sum.inl 2, -5), (Sum.inl 7, 80), (Sum.inl 3, 80), (Sum.inl 1, 190), (Sum.inr 977, -8640), (Sum.inr 1597, -8640), (Sum.inr 1897, -4320), (Sum.inr 1900, -4320), (Sum.inr 1907, -4320), (Sum.inr 1921, -4320), (Sum.inr 2016, -8640), (Sum.inr 2020, -8640), (Sum.inr 2052, -4320), (Sum.inr 2075, -8640), (Sum.inr 2106, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -8640), (Sum.inr 2242, -4320), (Sum.inr 2479, -4320), (Sum.inr 3459, -4320), (Sum.inr 3603, -4320), (Sum.inr 4392, 17280), (Sum.inr 4435, 17280), (Sum.inr 4797, 34560), (Sum.inr 4812, 34560), (Sum.inr 4815, 17280), (Sum.inr 4848, 34560), (Sum.inr 4851, 17280), (Sum.inr 5144, 34560)]

def numericRow1995 : Integer.Sparse Master := [(Sum.inr 932, -1), (Sum.inr 1087, -1), (Sum.inr 1681, -1), (Sum.inr 1739, -1), (Sum.inr 1814, -1), (Sum.inr 1966, -1), (Sum.inr 2028, -1), (Sum.inr 2051, -1), (Sum.inr 2054, -1), (Sum.inr 2058, -1), (Sum.inr 2157, -1), (Sum.inr 2177, -1), (Sum.inr 2191, -1), (Sum.inr 2206, -1), (Sum.inr 2215, -1), (Sum.inr 2216, -1), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2279, -2), (Sum.inr 2723, -1), (Sum.inr 3544, -1), (Sum.inr 4345, 4), (Sum.inr 4353, 4), (Sum.inr 4357, 4), (Sum.inr 4680, 4), (Sum.inr 4687, 4), (Sum.inr 4690, 4), (Sum.inr 4765, 4), (Sum.inr 4768, 4), (Sum.inr 4803, 4), (Sum.inr 4808, 4), (Sum.inr 4816, 4), (Sum.inr 4819, 4), (Sum.inr 4821, 4), (Sum.inr 5233, 4), (Sum.inr 5244, 4), (Sum.inr 5266, 4), (Sum.inr 5267, 4)]

def numericRow1996 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1681, 1), (Sum.inr 1682, 1), (Sum.inr 1686, 1), (Sum.inr 1739, 1), (Sum.inr 2145, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2162, 1), (Sum.inr 2177, 1), (Sum.inr 2178, 1), (Sum.inr 2179, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 1), (Sum.inr 2196, 1), (Sum.inr 2206, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2220, 1), (Sum.inr 2221, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1), (Sum.inr 2678, 1), (Sum.inr 2698, 1), (Sum.inr 2723, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1)]

def numericRow1997 : Integer.Sparse Master := [(Sum.inr 1806, 1), (Sum.inr 1813, 1), (Sum.inr 1814, 1), (Sum.inr 1816, 1), (Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

def numericRow1998 : Integer.Sparse Master := [(Sum.inl 0, 37), (Sum.inl 6, -5), (Sum.inl 2, 50), (Sum.inl 7, 80), (Sum.inl 3, 160), (Sum.inl 1, -70), (Sum.inr 1005, -4320), (Sum.inr 1623, -4320), (Sum.inr 1913, -4320), (Sum.inr 1922, -4320), (Sum.inr 1926, -4320), (Sum.inr 1929, -4320), (Sum.inr 1948, -4320), (Sum.inr 1949, -4320), (Sum.inr 2000, -8640), (Sum.inr 2023, -4320), (Sum.inr 2054, -4320), (Sum.inr 2058, -4320), (Sum.inr 2110, -4320), (Sum.inr 2206, -4320), (Sum.inr 2214, -4320), (Sum.inr 2216, -4320), (Sum.inr 2275, -4320), (Sum.inr 2515, -4320), (Sum.inr 2954, -4320), (Sum.inr 3479, -4320), (Sum.inr 3606, -4320), (Sum.inr 3613, -4320), (Sum.inr 4407, 17280), (Sum.inr 4410, 17280), (Sum.inr 4412, 17280), (Sum.inr 4471, 17280), (Sum.inr 4783, 17280), (Sum.inr 4785, 17280), (Sum.inr 4803, 17280), (Sum.inr 4806, 17280), (Sum.inr 4813, 17280), (Sum.inr 4836, 17280), (Sum.inr 4840, 17280), (Sum.inr 4842, 17280), (Sum.inr 4867, 17280), (Sum.inr 4870, 17280), (Sum.inr 5138, 17280), (Sum.inr 5173, 17280)]

def numericRow1999 : Integer.Sparse Master := [(Sum.inr 927, -1), (Sum.inr 1083, -1), (Sum.inr 1675, -1), (Sum.inr 1728, -1), (Sum.inr 1810, -1), (Sum.inr 1963, -1), (Sum.inr 2051, -1), (Sum.inr 2054, -2), (Sum.inr 2058, -1), (Sum.inr 2062, -1), (Sum.inr 2152, -1), (Sum.inr 2174, -1), (Sum.inr 2191, -1), (Sum.inr 2206, -2), (Sum.inr 2216, -1), (Sum.inr 2230, -1), (Sum.inr 2266, -1), (Sum.inr 2278, -1), (Sum.inr 2723, -1), (Sum.inr 2743, -1), (Sum.inr 3544, -1), (Sum.inr 3548, -1), (Sum.inr 4347, 4), (Sum.inr 4357, 4), (Sum.inr 4677, 4), (Sum.inr 4682, 4), (Sum.inr 4690, 4), (Sum.inr 4761, 4), (Sum.inr 4768, 4), (Sum.inr 4815, 4), (Sum.inr 4817, 4), (Sum.inr 4821, 4), (Sum.inr 5229, 4), (Sum.inr 5260, 4)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2000 : Integer.Sparse Master := [(Sum.inr 1675, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1728, 1), (Sum.inr 2142, 1), (Sum.inr 2152, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2174, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2206, 2), (Sum.inr 2207, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2230, 1), (Sum.inr 2266, 1), (Sum.inr 2673, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2743, 1)]

def numericRow2001 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 1808, 1), (Sum.inr 1810, 1), (Sum.inr 1816, 1), (Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 4084, -1)]

def numericRow2002 : Integer.Sparse Master := [(Sum.inl 0, 81), (Sum.inl 2, 20), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, 155), (Sum.inr 713, -4320), (Sum.inr 715, -4320), (Sum.inr 716, -4320), (Sum.inr 725, -4320), (Sum.inr 751, -4320), (Sum.inr 752, -4320), (Sum.inr 753, -4320), (Sum.inr 771, -4320), (Sum.inr 807, -8640), (Sum.inr 1771, -4320), (Sum.inr 1773, -4320), (Sum.inr 1774, -4320), (Sum.inr 1782, -4320), (Sum.inr 1838, -4320), (Sum.inr 1840, -4320), (Sum.inr 1841, -4320), (Sum.inr 1855, -4320), (Sum.inr 1863, -4320), (Sum.inr 1864, -4320), (Sum.inr 1871, -4320), (Sum.inr 1882, -4320), (Sum.inr 1883, -4320), (Sum.inr 1892, -4320), (Sum.inr 1909, -8640), (Sum.inr 2000, -8640), (Sum.inr 2003, -8640), (Sum.inr 2006, -8640), (Sum.inr 2020, -4320), (Sum.inr 2022, -4320), (Sum.inr 2029, -4320), (Sum.inr 2051, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -8640), (Sum.inr 2191, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -4320), (Sum.inr 2203, -4320), (Sum.inr 2206, -8640), (Sum.inr 2225, -4320), (Sum.inr 2244, -8640), (Sum.inr 2262, -8640), (Sum.inr 3705, -4320), (Sum.inr 3767, -4320), (Sum.inr 3781, -4320), (Sum.inr 3794, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320)]

def numericRow2003 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 6, -5), (Sum.inl 2, 30), (Sum.inl 8, 80), (Sum.inl 1, -20), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1909, -8640), (Sum.inr 1915, -4320), (Sum.inr 1946, -4320), (Sum.inr 1990, -4320), (Sum.inr 1997, -4320), (Sum.inr 2000, -8640), (Sum.inr 2020, -4320), (Sum.inr 2048, -4320), (Sum.inr 2058, -4320), (Sum.inr 2082, -4320), (Sum.inr 2107, -4320), (Sum.inr 2202, -4320), (Sum.inr 2216, -4320), (Sum.inr 2260, -4320), (Sum.inr 2512, -4320), (Sum.inr 2954, -4320), (Sum.inr 3471, -4320), (Sum.inr 3606, -4320), (Sum.inr 3607, -4320), (Sum.inr 4402, 17280), (Sum.inr 4453, 17280), (Sum.inr 4780, 17280), (Sum.inr 4799, 34560), (Sum.inr 4803, 17280), (Sum.inr 4829, 17280), (Sum.inr 4836, 17280), (Sum.inr 4861, 17280), (Sum.inr 4867, 17280), (Sum.inr 5164, 17280)]

def numericRow2004 : Integer.Sparse Master := [(Sum.inr 922, -1), (Sum.inr 930, -1), (Sum.inr 933, -2), (Sum.inr 1673, -1), (Sum.inr 1690, -1), (Sum.inr 1691, -2), (Sum.inr 1805, -1), (Sum.inr 1812, -1), (Sum.inr 1815, -2), (Sum.inr 1964, -1), (Sum.inr 1967, -2), (Sum.inr 2020, -2), (Sum.inr 2025, -2), (Sum.inr 2029, -2), (Sum.inr 2150, -1), (Sum.inr 2165, -1), (Sum.inr 2166, -2), (Sum.inr 2182, -1), (Sum.inr 2183, -2), (Sum.inr 2202, -2), (Sum.inr 2224, -2), (Sum.inr 2225, -2), (Sum.inr 2684, -1), (Sum.inr 2703, -1), (Sum.inr 2739, -2), (Sum.inr 3394, -1), (Sum.inr 3496, -1), (Sum.inr 3534, -2), (Sum.inr 4083, 4)]

def numericRow2005 : Integer.Sparse Master := [(Sum.inr 919, -1), (Sum.inr 924, -1), (Sum.inr 927, -1), (Sum.inr 932, -1), (Sum.inr 1664, -1), (Sum.inr 1674, -1), (Sum.inr 1675, -1), (Sum.inr 1681, -1), (Sum.inr 1802, -1), (Sum.inr 1807, -1), (Sum.inr 1810, -1), (Sum.inr 1814, -1), (Sum.inr 1960, -1), (Sum.inr 1963, -1), (Sum.inr 1966, -1), (Sum.inr 2019, -1), (Sum.inr 2022, -1), (Sum.inr 2028, -1), (Sum.inr 2051, -1), (Sum.inr 2054, -1), (Sum.inr 2058, -1), (Sum.inr 2141, -1), (Sum.inr 2151, -1), (Sum.inr 2152, -1), (Sum.inr 2157, -1), (Sum.inr 2173, -1), (Sum.inr 2174, -1), (Sum.inr 2177, -1), (Sum.inr 2190, -1), (Sum.inr 2191, -1), (Sum.inr 2203, -1), (Sum.inr 2206, -1), (Sum.inr 2215, -1), (Sum.inr 2216, -1), (Sum.inr 2672, -1), (Sum.inr 2694, -1), (Sum.inr 2722, -1), (Sum.inr 2723, -1), (Sum.inr 3391, -1), (Sum.inr 3493, -1), (Sum.inr 3533, -1), (Sum.inr 3544, -1), (Sum.inr 4084, 4)]

def numericRow2006 : Integer.Sparse Master := [(Sum.inr 921, -1), (Sum.inr 1080, -1), (Sum.inr 1666, -1), (Sum.inr 1710, -1), (Sum.inr 1804, -1), (Sum.inr 1959, -1), (Sum.inr 2052, -3), (Sum.inr 2065, -2), (Sum.inr 2143, -1), (Sum.inr 2170, -1), (Sum.inr 2193, -3), (Sum.inr 2218, -2), (Sum.inr 2247, -1), (Sum.inr 2290, -1), (Sum.inr 2726, -2), (Sum.inr 3545, -2), (Sum.inr 4348, 8), (Sum.inr 4675, 4), (Sum.inr 4683, 8), (Sum.inr 4762, 8), (Sum.inr 4830, 4), (Sum.inr 4836, 8), (Sum.inr 5222, 4), (Sum.inr 5252, 4)]

def numericRow2007 : Integer.Sparse Master := [(Sum.inr 1666, 1), (Sum.inr 1669, 2), (Sum.inr 1710, 1), (Sum.inr 2139, 1), (Sum.inr 2143, 1), (Sum.inr 2146, 2), (Sum.inr 2170, 1), (Sum.inr 2171, 2), (Sum.inr 2187, 1), (Sum.inr 2193, 3), (Sum.inr 2197, 2), (Sum.inr 2218, 2), (Sum.inr 2247, 1), (Sum.inr 2664, 1), (Sum.inr 2712, 1), (Sum.inr 2726, 2)]

def numericRow2008 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 1804, 1), (Sum.inr 1809, 2), (Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 4085, -1)]

def numericRow2009 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 2050, 1), (Sum.inr 2052, 3), (Sum.inr 4085, -1)]

def numericRow2010 : Integer.Sparse Master := [(Sum.inr 900, -1), (Sum.inr 901, -2), (Sum.inr 915, -1), (Sum.inr 1588, -1), (Sum.inr 1589, -2), (Sum.inr 1632, -1), (Sum.inr 1786, -1), (Sum.inr 1787, -2), (Sum.inr 1798, -1), (Sum.inr 1982, -1), (Sum.inr 1983, -2), (Sum.inr 1987, -2), (Sum.inr 1990, -2), (Sum.inr 1996, -2), (Sum.inr 1997, -2), (Sum.inr 2000, -4), (Sum.inr 2016, -2), (Sum.inr 2046, -1), (Sum.inr 2067, -1), (Sum.inr 2075, -2), (Sum.inr 2077, -1), (Sum.inr 2536, -1), (Sum.inr 2553, -2), (Sum.inr 2556, -1), (Sum.inr 3370, -1), (Sum.inr 3514, -2), (Sum.inr 3521, -1), (Sum.inr 4080, 4)]

def numericRow2011 : Integer.Sparse Master := [(Sum.inr 879, -2), (Sum.inr 885, -1), (Sum.inr 998, -1), (Sum.inr 1556, -2), (Sum.inr 1563, -1), (Sum.inr 1600, -1), (Sum.inr 1771, -2), (Sum.inr 1776, -1), (Sum.inr 1838, -2), (Sum.inr 1844, -1), (Sum.inr 1909, -4), (Sum.inr 1913, -4), (Sum.inr 1922, -4), (Sum.inr 1925, -2), (Sum.inr 2020, -2), (Sum.inr 2023, -1), (Sum.inr 2202, -2), (Sum.inr 2214, -1), (Sum.inr 2383, -1), (Sum.inr 2480, -2), (Sum.inr 2483, -1), (Sum.inr 3352, -1), (Sum.inr 3467, -2), (Sum.inr 3477, -1), (Sum.inr 4080, 4)]

def numericRow2012 : Integer.Sparse Master := [(Sum.inr 4063, 1), (Sum.inr 4064, 1), (Sum.inr 4065, 2), (Sum.inr 4069, 1), (Sum.inr 4073, 1), (Sum.inr 4074, 1), (Sum.inr 4075, 2), (Sum.inr 4077, 1), (Sum.inr 4078, 2), (Sum.inr 4079, 1), (Sum.inr 4080, 5), (Sum.inr 4081, 2), (Sum.inr 4082, 2), (Sum.inr 4083, 1), (Sum.inr 4084, 2), (Sum.inr 4088, 1), (Sum.inr 4090, 1), (Sum.inr 4091, 1), (Sum.inr 4092, 2)]

def numericRow2013 : Integer.Sparse Master := [(Sum.inr 3128, 3), (Sum.inr 3130, 1), (Sum.inr 3155, 1), (Sum.inr 3390, 1), (Sum.inr 4083, -1)]

def numericRow2014 : Integer.Sparse Master := [(Sum.inl 0, 489), (Sum.inl 5, -60), (Sum.inl 6, -45), (Sum.inl 2, 280), (Sum.inl 8, 480), (Sum.inl 3, -640), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 12, -480), (Sum.inl 4, -640), (Sum.inl 27, 180), (Sum.inl 1, -140), (Sum.inr 1126, -8640), (Sum.inr 1129, -8640), (Sum.inr 2807, -8640), (Sum.inr 2809, -8640), (Sum.inr 2924, -17280), (Sum.inr 3256, -8640), (Sum.inr 3263, -8640), (Sum.inr 3307, -4320), (Sum.inr 3587, -8640), (Sum.inr 3590, -8640), (Sum.inr 3605, -17280), (Sum.inr 3607, -17280), (Sum.inr 3613, -8640), (Sum.inr 3622, -8640), (Sum.inr 3890, -4320), (Sum.inr 3901, -8640)]

def numericRow2015 : Integer.Sparse Master := [(Sum.inl 0, 504), (Sum.inl 5, -60), (Sum.inl 6, -30), (Sum.inl 2, 110), (Sum.inl 7, 160), (Sum.inl 8, 80), (Sum.inl 3, 160), (Sum.inl 24, 240), (Sum.inl 4, -320), (Sum.inl 27, 180), (Sum.inl 1, 740), (Sum.inl 30, 480), (Sum.inr 919, -8640), (Sum.inr 922, -8640), (Sum.inr 1039, -4320), (Sum.inr 1664, -8640), (Sum.inr 1673, -8640), (Sum.inr 1706, -4320), (Sum.inr 2330, -8640), (Sum.inr 2332, -8640), (Sum.inr 2553, -17280), (Sum.inr 2556, -8640), (Sum.inr 2721, -8640), (Sum.inr 3404, -8640), (Sum.inr 3410, -8640), (Sum.inr 3514, -17280), (Sum.inr 3521, -8640), (Sum.inr 3532, -8640), (Sum.inr 3603, -8640), (Sum.inr 3607, -17280), (Sum.inr 3622, -8640), (Sum.inr 4041, -4320), (Sum.inr 4046, -8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2016 : Integer.Sparse Master := [(Sum.inr 1293, -1), (Sum.inr 2556, -3), (Sum.inr 2764, -3), (Sum.inr 3304, -1), (Sum.inr 3521, -3), (Sum.inr 3581, -3), (Sum.inr 3731, -1), (Sum.inr 3849, -3), (Sum.inr 3867, -1), (Sum.inr 3875, -3), (Sum.inr 4540, 4), (Sum.inr 4542, 12), (Sum.inr 4964, 12), (Sum.inr 4975, 4), (Sum.inr 5145, 24), (Sum.inr 5150, 12)]

def numericRow2017 : Integer.Sparse Master := [(Sum.inr 2688, 1), (Sum.inr 2690, 1), (Sum.inr 2700, 3), (Sum.inr 3257, 3), (Sum.inr 3304, 1), (Sum.inr 3521, 3), (Sum.inr 3554, 3), (Sum.inr 3562, 6), (Sum.inr 3581, 3), (Sum.inr 3867, 1), (Sum.inr 3875, 3)]

def numericRow2018 : Integer.Sparse Master := [(Sum.inl 0, 86), (Sum.inl 6, -5), (Sum.inl 2, 45), (Sum.inl 7, 80), (Sum.inl 3, 240), (Sum.inl 4, 160), (Sum.inl 1, -120), (Sum.inr 915, -4320), (Sum.inr 929, -1440), (Sum.inr 1034, -1440), (Sum.inr 1632, -4320), (Sum.inr 1644, -1440), (Sum.inr 1680, -1440), (Sum.inr 2328, -4320), (Sum.inr 2338, -1440), (Sum.inr 2536, -4320), (Sum.inr 2590, -8640), (Sum.inr 2671, -1440), (Sum.inr 2764, -4320), (Sum.inr 3370, -4320), (Sum.inr 3390, -1440), (Sum.inr 3401, -4320), (Sum.inr 3416, -1440), (Sum.inr 3564, -8640), (Sum.inr 3581, -4320), (Sum.inr 3613, -4320), (Sum.inr 3909, -1440), (Sum.inr 4010, -4320), (Sum.inr 4025, -1440)]

def numericRow2019 : Integer.Sparse Master := [(Sum.inr 1039, -1), (Sum.inr 1706, -1), (Sum.inr 2107, -4), (Sum.inr 2110, -2), (Sum.inr 2243, -4), (Sum.inr 2260, -4), (Sum.inr 2275, -2), (Sum.inr 2764, -2), (Sum.inr 3581, -2), (Sum.inr 4364, 8), (Sum.inr 4366, 8), (Sum.inr 4696, 8), (Sum.inr 4698, 8), (Sum.inr 4851, 8), (Sum.inr 4852, 16), (Sum.inr 5278, 4), (Sum.inr 5281, 8)]

def numericRow2020 : Integer.Sparse Master := [(Sum.inr 1703, 2), (Sum.inr 1706, 1), (Sum.inr 1711, 2), (Sum.inr 2238, 2), (Sum.inr 2240, 2), (Sum.inr 2243, 2), (Sum.inr 2248, 2), (Sum.inr 2250, 4), (Sum.inr 2260, 4), (Sum.inr 2275, 2), (Sum.inr 2747, 1), (Sum.inr 2750, 2), (Sum.inr 2764, 2)]

def numericRow2021 : Integer.Sparse Master := [(Sum.inl 0, 106), (Sum.inl 5, -60), (Sum.inl 2, 20), (Sum.inl 7, -240), (Sum.inl 3, -320), (Sum.inl 23, 240), (Sum.inl 24, 480), (Sum.inl 27, 180), (Sum.inl 1, -190), (Sum.inr 730, -8640), (Sum.inr 732, -8640), (Sum.inr 780, -8640), (Sum.inr 786, -4320), (Sum.inr 798, -8640), (Sum.inr 822, -4320), (Sum.inr 1802, -8640), (Sum.inr 1805, -8640), (Sum.inr 2016, -17280), (Sum.inr 2023, -8640), (Sum.inr 2046, -8640), (Sum.inr 2075, -17280), (Sum.inr 2077, -8640), (Sum.inr 2106, -8640), (Sum.inr 2107, -17280), (Sum.inr 2141, -8640), (Sum.inr 2150, -8640), (Sum.inr 2214, -8640), (Sum.inr 2242, -8640), (Sum.inr 2245, -8640), (Sum.inr 2260, -17280), (Sum.inr 2277, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3890, -4320), (Sum.inr 3910, -8640)]

def numericRow2022 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 6, 15), (Sum.inl 2, -110), (Sum.inl 7, -80), (Sum.inl 8, -160), (Sum.inl 3, -160), (Sum.inl 1, -70), (Sum.inr 1034, -8640), (Sum.inr 1644, -8640), (Sum.inr 2051, -8640), (Sum.inr 2100, -17280), (Sum.inr 2105, -17280), (Sum.inr 2191, -8640), (Sum.inr 2241, -17280), (Sum.inr 2880, -8640), (Sum.inr 3602, -4320), (Sum.inr 3617, -8640), (Sum.inr 4436, 34560), (Sum.inr 4441, 17280), (Sum.inr 4849, 69120), (Sum.inr 4854, 34560), (Sum.inr 4863, 34560), (Sum.inr 4878, 34560), (Sum.inr 5197, 34560)]

def numericRow2023 : Integer.Sparse Master := [(Sum.inr 919, -1), (Sum.inr 1079, -1), (Sum.inr 1664, -1), (Sum.inr 1708, -1), (Sum.inr 1802, -1), (Sum.inr 2019, -1), (Sum.inr 2054, -2), (Sum.inr 2058, -2), (Sum.inr 2141, -1), (Sum.inr 2190, -1), (Sum.inr 2206, -2), (Sum.inr 2216, -2), (Sum.inr 2244, -1), (Sum.inr 2245, -1), (Sum.inr 2262, -1), (Sum.inr 2277, -1), (Sum.inr 2723, -2), (Sum.inr 3544, -2), (Sum.inr 4345, 8), (Sum.inr 4677, 4), (Sum.inr 4680, 8), (Sum.inr 4803, 8), (Sum.inr 4815, 4), (Sum.inr 4816, 8), (Sum.inr 5220, 4), (Sum.inr 5251, 4)]

def numericRow2024 : Integer.Sparse Master := [(Sum.inr 1664, 1), (Sum.inr 1668, 2), (Sum.inr 1708, 1), (Sum.inr 2141, 1), (Sum.inr 2142, 1), (Sum.inr 2145, 2), (Sum.inr 2190, 1), (Sum.inr 2192, 1), (Sum.inr 2195, 2), (Sum.inr 2196, 2), (Sum.inr 2206, 2), (Sum.inr 2216, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2662, 1), (Sum.inr 2710, 1), (Sum.inr 2723, 2)]

def numericRow2025 : Integer.Sparse Master := [(Sum.inr 4063, 4), (Sum.inr 4068, 1), (Sum.inr 4073, 4), (Sum.inr 4080, 12), (Sum.inr 4083, 4), (Sum.inr 4087, 1), (Sum.inr 4091, 4)]

def numericRow2026 : Integer.Sparse Master := [(Sum.inr 1814, 1), (Sum.inr 3131, 1), (Sum.inr 3365, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

def numericRow2027 : Integer.Sparse Master := [(Sum.inr 2362, 1), (Sum.inr 3032, 1), (Sum.inr 3033, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

def numericRow2028 : Integer.Sparse Master := [(Sum.inr 2343, 1), (Sum.inr 2819, 1), (Sum.inr 3673, 1), (Sum.inr 3699, 1), (Sum.inr 3705, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

def numericRow2029 : Integer.Sparse Master := [(Sum.inr 2324, 1), (Sum.inr 2801, 1), (Sum.inr 3676, 1), (Sum.inr 3685, 1), (Sum.inr 3690, 1), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

def numericRow2030 : Integer.Sparse Master := [(Sum.inr 2350, 1), (Sum.inr 3134, 1), (Sum.inr 3708, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3722, 1), (Sum.inr 4092, -1)]

def numericRow2031 : Integer.Sparse Master := [(Sum.inr 2824, 2), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3779, 1), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2032 : Integer.Sparse Master := [(Sum.inr 2351, 1), (Sum.inr 3135, 1), (Sum.inr 3709, 1), (Sum.inr 3716, 1), (Sum.inr 3721, 2), (Sum.inr 4091, -1)]

def numericRow2033 : Integer.Sparse Master := [(Sum.inl 0, 180), (Sum.inl 23, -720), (Sum.inl 27, -180), (Sum.inl 1, 720), (Sum.inr 1814, -12960), (Sum.inr 1817, -3240), (Sum.inr 1819, -6480), (Sum.inr 2115, -6480), (Sum.inr 2157, -12960), (Sum.inr 2159, -3240), (Sum.inr 2169, -6480), (Sum.inr 2276, -6480), (Sum.inr 2817, -12960), (Sum.inr 2820, -3240), (Sum.inr 3591, -12960), (Sum.inr 3596, -3240), (Sum.inr 3614, -6480), (Sum.inr 3708, -6480), (Sum.inr 3732, -12960), (Sum.inr 3791, -6480), (Sum.inr 3811, -12960), (Sum.inr 3886, -6480), (Sum.inr 3891, -12960), (Sum.inr 3907, -6480)]

def numericRow2034 : Integer.Sparse Master := [(Sum.inl 0, -180), (Sum.inl 23, 720), (Sum.inl 27, 180), (Sum.inl 1, -720), (Sum.inr 1814, 12960), (Sum.inr 1817, 3240), (Sum.inr 1819, 6480), (Sum.inr 2115, 6480), (Sum.inr 2817, 12960), (Sum.inr 2820, 3240), (Sum.inr 3708, 6480), (Sum.inr 3732, 12960), (Sum.inr 3886, 3240)]

def numericRow2035 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -45), (Sum.inr 2686, -6480), (Sum.inr 3397, -6480), (Sum.inr 3693, -12960), (Sum.inr 3770, -12960), (Sum.inr 3894, -3240), (Sum.inr 5232, 51840), (Sum.inr 5235, 12960), (Sum.inr 5297, 12960), (Sum.inr 5376, 12960)]

def numericRow2036 : Integer.Sparse Master := [(Sum.inl 0, 108), (Sum.inl 24, -360), (Sum.inl 27, -90), (Sum.inl 1, -90), (Sum.inr 1815, -2160), (Sum.inr 1818, -2160), (Sum.inr 2116, -1080), (Sum.inr 2166, -2160), (Sum.inr 2168, -2160), (Sum.inr 2288, -1080), (Sum.inr 2341, -4320), (Sum.inr 2345, -2160), (Sum.inr 2818, -2160), (Sum.inr 3417, -4320), (Sum.inr 3423, -2160), (Sum.inr 3592, -2160), (Sum.inr 3614, -2160), (Sum.inr 3616, -1080), (Sum.inr 3709, -2160), (Sum.inr 3790, -2160), (Sum.inr 3792, -2160), (Sum.inr 3815, -2160), (Sum.inr 3892, -4320), (Sum.inr 3898, -2160), (Sum.inr 3913, -2160)]

def numericRow2037 : Integer.Sparse Master := [(Sum.inl 0, -108), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, 90), (Sum.inr 1815, 2160), (Sum.inr 1818, 2160), (Sum.inr 2116, 1080), (Sum.inr 2341, 4320), (Sum.inr 2345, 2160), (Sum.inr 2818, 2160), (Sum.inr 3709, 2160), (Sum.inr 3790, 2160)]

def numericRow2038 : Integer.Sparse Master := [(Sum.inl 0, 20), (Sum.inl 23, 192), (Sum.inl 27, 72), (Sum.inl 1, 100), (Sum.inl 30, 96), (Sum.inr 2686, -3456), (Sum.inr 3397, -3456), (Sum.inr 3693, -6912), (Sum.inr 3694, -3456), (Sum.inr 3770, -6912), (Sum.inr 3773, -3456), (Sum.inr 3893, -1728), (Sum.inr 4043, -864), (Sum.inr 5236, 13824), (Sum.inr 5303, 3456), (Sum.inr 5377, 6912)]

def numericRow2039 : Integer.Sparse Master := [(Sum.inr 2341, -1), (Sum.inr 2488, -1), (Sum.inr 2561, -1), (Sum.inr 2817, -1), (Sum.inr 3417, -1), (Sum.inr 3478, -1), (Sum.inr 3522, -1), (Sum.inr 3591, -1), (Sum.inr 3671, -1), (Sum.inr 3689, -1), (Sum.inr 3706, -1), (Sum.inr 3719, -1), (Sum.inr 3732, -1), (Sum.inr 3754, -1), (Sum.inr 3757, -1), (Sum.inr 3771, -1), (Sum.inr 3795, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 3845, -2), (Sum.inr 4668, 4), (Sum.inr 4669, 4), (Sum.inr 4670, 4), (Sum.inr 4690, 4), (Sum.inr 4856, 4), (Sum.inr 4931, 4), (Sum.inr 4934, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4959, 4), (Sum.inr 4966, 4), (Sum.inr 5188, 4), (Sum.inr 5339, 4), (Sum.inr 5353, 4), (Sum.inr 5379, 4), (Sum.inr 5385, 4), (Sum.inr 5446, 4)]

def numericRow2040 : Integer.Sparse Master := [(Sum.inl 0, -630), (Sum.inl 2, -270), (Sum.inl 23, -1440), (Sum.inl 24, -1440), (Sum.inl 55, -1440), (Sum.inl 27, 1080), (Sum.inl 1, 360), (Sum.inr 1794, 8640), (Sum.inr 1795, 8640), (Sum.inr 1796, 8640), (Sum.inr 1816, 8640), (Sum.inr 2094, 8640), (Sum.inr 2350, 8640), (Sum.inr 2352, 8640), (Sum.inr 2620, 8640), (Sum.inr 2801, 8640), (Sum.inr 2802, 8640), (Sum.inr 2819, 8640), (Sum.inr 2824, 8640), (Sum.inr 3710, 8640), (Sum.inr 3724, 8640), (Sum.inr 3733, 8640), (Sum.inr 3783, 8640), (Sum.inr 3881, 8640)]

def numericRow2041 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2155, 1), (Sum.inr 2158, 1), (Sum.inr 2164, 1), (Sum.inr 2274, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3512, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3555, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3757, 1), (Sum.inr 3760, 1), (Sum.inr 3761, 1), (Sum.inr 3771, 1), (Sum.inr 3795, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3845, 1), (Sum.inr 3868, 1), (Sum.inr 3884, 1)]

def numericRow2042 : Integer.Sparse Master := [(Sum.inr 2348, 1), (Sum.inr 3133, 1), (Sum.inr 3671, 1), (Sum.inr 3693, 1), (Sum.inr 3719, 1), (Sum.inr 3720, 1), (Sum.inr 4092, -1)]

def numericRow2043 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2798, 1), (Sum.inr 3674, 1), (Sum.inr 3689, 1), (Sum.inr 3691, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

def numericRow2044 : Integer.Sparse Master := [(Sum.inr 2356, 1), (Sum.inr 3138, 1), (Sum.inr 3674, 1), (Sum.inr 3693, 1), (Sum.inr 3732, 1), (Sum.inr 3733, 1), (Sum.inr 4092, -1)]

def numericRow2045 : Integer.Sparse Master := [(Sum.inr 1810, -2), (Sum.inr 1818, -1), (Sum.inr 1819, -1), (Sum.inr 2152, -2), (Sum.inr 2168, -1), (Sum.inr 2169, -1), (Sum.inr 2522, -1), (Sum.inr 2672, -2), (Sum.inr 2685, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -1), (Sum.inr 3054, -1), (Sum.inr 3391, -2), (Sum.inr 3498, -2), (Sum.inr 3548, -1), (Sum.inr 3626, -1), (Sum.inr 4703, 8), (Sum.inr 4704, 4), (Sum.inr 4705, 4), (Sum.inr 4884, 4), (Sum.inr 4945, 8), (Sum.inr 4976, 8), (Sum.inr 5206, 4), (Sum.inr 5215, 8), (Sum.inr 5229, 8), (Sum.inr 5287, 8), (Sum.inr 5300, 4)]

def numericRow2046 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 2, 150), (Sum.inl 55, 480), (Sum.inl 27, 120), (Sum.inl 1, 120), (Sum.inr 1829, 2880), (Sum.inr 1830, 1440), (Sum.inr 1831, 1440), (Sum.inr 2138, 1440), (Sum.inr 2362, 2880), (Sum.inr 2643, 1440), (Sum.inr 2758, 2880), (Sum.inr 2774, 1440), (Sum.inr 2831, 2880), (Sum.inr 3083, 2880), (Sum.inr 3092, 2880)]

def numericRow2047 : Integer.Sparse Master := [(Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2272, 2), (Sum.inr 2273, 1), (Sum.inr 2280, 1), (Sum.inr 2286, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2672, 2), (Sum.inr 2673, 2), (Sum.inr 2685, 1), (Sum.inr 2687, 1), (Sum.inr 2705, 2), (Sum.inr 2743, 1), (Sum.inr 3025, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2048 : Integer.Sparse Master := [(Sum.inl 0, 528), (Sum.inl 27, -360), (Sum.inl 1, 120), (Sum.inl 30, -1440), (Sum.inr 2342, -25920), (Sum.inr 2344, -12960), (Sum.inr 3421, -25920), (Sum.inr 3422, -12960), (Sum.inr 3616, -12960), (Sum.inr 4042, -25920)]

def numericRow2049 : Integer.Sparse Master := [(Sum.inl 0, -528), (Sum.inl 27, 360), (Sum.inl 1, -120), (Sum.inl 30, 1440), (Sum.inr 2342, 25920), (Sum.inr 2344, 12960)]

def numericRow2050 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -45), (Sum.inr 3694, -12960), (Sum.inr 3773, -12960), (Sum.inr 3894, -3240)]

def numericRow2051 : Integer.Sparse Master := [(Sum.inr 2342, -1), (Sum.inr 2489, -1), (Sum.inr 2818, -1), (Sum.inr 2931, -2), (Sum.inr 3421, -1), (Sum.inr 3482, -1), (Sum.inr 3592, -1), (Sum.inr 3612, -2), (Sum.inr 3672, -1), (Sum.inr 3690, -2), (Sum.inr 3756, -1), (Sum.inr 3764, -2), (Sum.inr 3779, -1), (Sum.inr 3790, -1), (Sum.inr 3797, -1), (Sum.inr 3815, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4933, 8), (Sum.inr 4934, 8), (Sum.inr 4935, 8), (Sum.inr 4951, 8), (Sum.inr 4958, 4), (Sum.inr 5189, 4), (Sum.inr 5340, 4), (Sum.inr 5463, 4)]

def numericRow2052 : Integer.Sparse Master := [(Sum.inr 3414, 2), (Sum.inr 3415, 2), (Sum.inr 3418, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3482, 1), (Sum.inr 3511, 1), (Sum.inr 3542, 1), (Sum.inr 3592, 1), (Sum.inr 3612, 2), (Sum.inr 3756, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3960, 1), (Sum.inr 3961, 2)]

def numericRow2053 : Integer.Sparse Master := [(Sum.inr 2822, 2), (Sum.inr 3672, 1), (Sum.inr 3694, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

def numericRow2054 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 3675, 1), (Sum.inr 3690, 2), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

def numericRow2055 : Integer.Sparse Master := [(Sum.inr 2827, 2), (Sum.inr 3675, 1), (Sum.inr 3694, 1), (Sum.inr 3790, 1), (Sum.inr 3929, 1), (Sum.inr 4091, -1)]

def numericRow2056 : Integer.Sparse Master := [(Sum.inr 2337, -4), (Sum.inr 2344, -1), (Sum.inr 2345, -2), (Sum.inr 2813, -4), (Sum.inr 2820, -1), (Sum.inr 2889, -2), (Sum.inr 3412, -4), (Sum.inr 3422, -1), (Sum.inr 3423, -2), (Sum.inr 3595, -4), (Sum.inr 3596, -1), (Sum.inr 3631, -2), (Sum.inr 3670, -2), (Sum.inr 3705, -4), (Sum.inr 3753, -2), (Sum.inr 3767, -4), (Sum.inr 3963, -2), (Sum.inr 4092, 4)]

def numericRow2057 : Integer.Sparse Master := [(Sum.inr 3412, 4), (Sum.inr 3422, 1), (Sum.inr 3423, 2), (Sum.inr 3595, 4), (Sum.inr 3596, 1), (Sum.inr 3631, 2), (Sum.inr 3753, 2), (Sum.inr 3767, 4), (Sum.inr 3963, 1), (Sum.inr 4092, 1)]

def numericRow2058 : Integer.Sparse Master := [(Sum.inr 4075, 8), (Sum.inr 4076, 4), (Sum.inr 4082, 4), (Sum.inr 4086, 2), (Sum.inr 4088, 8), (Sum.inr 4092, 4)]

def numericRow2059 : Integer.Sparse Master := [(Sum.inl 0, 342), (Sum.inl 5, -60), (Sum.inl 2, 30), (Sum.inl 7, -240), (Sum.inl 3, -480), (Sum.inl 23, 720), (Sum.inl 12, -240), (Sum.inl 27, 180), (Sum.inl 1, 1800), (Sum.inr 1811, -4320), (Sum.inr 1812, -4320), (Sum.inr 1814, -8640), (Sum.inr 2110, -4320), (Sum.inr 2156, -4320), (Sum.inr 2157, -8640), (Sum.inr 2165, -4320), (Sum.inr 2275, -4320), (Sum.inr 2814, -4320), (Sum.inr 2815, -4320), (Sum.inr 2817, -8640), (Sum.inr 2896, -4320), (Sum.inr 3585, -4320), (Sum.inr 3588, -4320), (Sum.inr 3591, -8640), (Sum.inr 3597, -4320), (Sum.inr 3603, -4320), (Sum.inr 3614, -8640), (Sum.inr 3708, -8640), (Sum.inr 3731, -4320), (Sum.inr 3732, -8640), (Sum.inr 3789, -4320), (Sum.inr 3791, -8640), (Sum.inr 3810, -4320), (Sum.inr 3811, -8640), (Sum.inr 3867, -4320), (Sum.inr 3885, -8640), (Sum.inr 3891, -8640), (Sum.inr 3893, -8640), (Sum.inr 3895, -4320), (Sum.inr 3902, -4320), (Sum.inr 3907, -8640)]

def numericRow2060 : Integer.Sparse Master := [(Sum.inl 0, 90), (Sum.inl 5, -12), (Sum.inl 2, 6), (Sum.inl 7, -48), (Sum.inl 3, -96), (Sum.inl 23, 144), (Sum.inl 12, -48), (Sum.inl 27, 36), (Sum.inl 1, -180), (Sum.inr 1802, -1296), (Sum.inr 1804, -1296), (Sum.inr 1810, -2592), (Sum.inr 1966, -1296), (Sum.inr 1970, -1296), (Sum.inr 2028, -2592), (Sum.inr 2106, -1296), (Sum.inr 2141, -1296), (Sum.inr 2143, -1296), (Sum.inr 2152, -2592), (Sum.inr 2177, -1296), (Sum.inr 2186, -1296), (Sum.inr 2215, -2592), (Sum.inr 2242, -1296), (Sum.inr 2807, -1296), (Sum.inr 2813, -2592), (Sum.inr 3590, -1296), (Sum.inr 3595, -2592), (Sum.inr 3613, -1296), (Sum.inr 3671, -2592), (Sum.inr 3693, -2592), (Sum.inr 3719, -2592), (Sum.inr 3754, -2592), (Sum.inr 3770, -2592), (Sum.inr 3786, -1296), (Sum.inr 3795, -2592), (Sum.inr 3799, -1296), (Sum.inr 3850, -5184), (Sum.inr 3890, -1296), (Sum.inr 3892, -2592), (Sum.inr 3897, -1296), (Sum.inr 3906, -2592), (Sum.inr 3910, -1296)]

def numericRow2061 : Integer.Sparse Master := [(Sum.inl 0, 63), (Sum.inl 5, 30), (Sum.inl 2, -10), (Sum.inl 7, 80), (Sum.inl 8, 40), (Sum.inl 3, 160), (Sum.inl 24, -360), (Sum.inl 4, 80), (Sum.inl 27, -90), (Sum.inl 1, -125), (Sum.inr 2672, -4320), (Sum.inr 2684, -2160), (Sum.inr 2705, -2160), (Sum.inr 3391, -4320), (Sum.inr 3394, -2160), (Sum.inr 3498, -2160), (Sum.inr 3689, -2160), (Sum.inr 3692, -2160), (Sum.inr 3706, -4320), (Sum.inr 3719, -4320), (Sum.inr 3721, -2160), (Sum.inr 3732, -4320), (Sum.inr 3757, -2160), (Sum.inr 3769, -2160), (Sum.inr 3771, -4320), (Sum.inr 3795, -4320), (Sum.inr 3811, -4320), (Sum.inr 3836, -2160), (Sum.inr 3892, -4320), (Sum.inr 3898, -2160), (Sum.inr 5219, 8640), (Sum.inr 5222, 8640), (Sum.inr 5231, 8640), (Sum.inr 5233, 17280), (Sum.inr 5243, 8640), (Sum.inr 5264, 17280), (Sum.inr 5279, 8640), (Sum.inr 5381, 17280)]

def numericRow2062 : Integer.Sparse Master := [(Sum.inl 0, 423), (Sum.inl 5, -60), (Sum.inl 2, 30), (Sum.inl 7, -240), (Sum.inl 3, -480), (Sum.inl 24, 720), (Sum.inl 4, -240), (Sum.inl 27, 180), (Sum.inl 1, -225), (Sum.inr 1805, -4320), (Sum.inr 1807, -4320), (Sum.inr 1810, -4320), (Sum.inr 1815, -4320), (Sum.inr 2107, -4320), (Sum.inr 2150, -4320), (Sum.inr 2151, -4320), (Sum.inr 2152, -4320), (Sum.inr 2166, -4320), (Sum.inr 2260, -4320), (Sum.inr 2431, -4320), (Sum.inr 2434, -4320), (Sum.inr 2488, -4320), (Sum.inr 2809, -4320), (Sum.inr 2813, -4320), (Sum.inr 2818, -4320), (Sum.inr 3453, -4320), (Sum.inr 3457, -4320), (Sum.inr 3478, -4320), (Sum.inr 3587, -4320), (Sum.inr 3592, -4320), (Sum.inr 3595, -4320), (Sum.inr 3607, -4320), (Sum.inr 3614, -4320), (Sum.inr 3671, -4320), (Sum.inr 3693, -4320), (Sum.inr 3709, -4320), (Sum.inr 3721, -4320), (Sum.inr 3754, -4320), (Sum.inr 3770, -4320), (Sum.inr 3787, -4320), (Sum.inr 3792, -4320), (Sum.inr 3804, -4320), (Sum.inr 3836, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3890, -4320), (Sum.inr 3891, -4320), (Sum.inr 3892, -8640), (Sum.inr 3894, -4320), (Sum.inr 3896, -4320), (Sum.inr 3903, -4320), (Sum.inr 3910, -4320), (Sum.inr 3913, -4320)]

def numericRow2063 : Integer.Sparse Master := [(Sum.inl 0, 978), (Sum.inl 5, 480), (Sum.inl 2, -180), (Sum.inl 7, 1440), (Sum.inl 8, 480), (Sum.inl 3, 2880), (Sum.inl 23, -2880), (Sum.inl 24, -1440), (Sum.inl 12, 960), (Sum.inl 4, 480), (Sum.inl 27, -1440), (Sum.inl 1, 1050), (Sum.inl 30, -1440), (Sum.inr 2672, -51840), (Sum.inr 2684, -51840), (Sum.inr 3391, -51840), (Sum.inr 3394, -51840), (Sum.inr 3690, -51840), (Sum.inr 3705, -51840), (Sum.inr 3719, -51840), (Sum.inr 3721, -51840), (Sum.inr 3732, -51840), (Sum.inr 3764, -51840), (Sum.inr 3767, -51840), (Sum.inr 3795, -51840), (Sum.inr 3811, -51840), (Sum.inr 3836, -51840), (Sum.inr 3891, -51840), (Sum.inr 3892, -25920), (Sum.inr 4042, -25920), (Sum.inr 5226, 207360), (Sum.inr 5229, 207360), (Sum.inr 5288, 103680), (Sum.inr 5379, 207360), (Sum.inr 5385, 103680)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2064 : Integer.Sparse Master := [(Sum.inr 2488, -1), (Sum.inr 2590, -1), (Sum.inr 3478, -1), (Sum.inr 3564, -1), (Sum.inr 3693, -1), (Sum.inr 3719, -1), (Sum.inr 3770, -1), (Sum.inr 3786, -1), (Sum.inr 3795, -1), (Sum.inr 3799, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3850, -2), (Sum.inr 3857, -1), (Sum.inr 3876, -1), (Sum.inr 4680, 4), (Sum.inr 4682, 4), (Sum.inr 4683, 4), (Sum.inr 4690, 4), (Sum.inr 4867, 4), (Sum.inr 4963, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 4976, 4), (Sum.inr 5042, 4), (Sum.inr 5188, 4), (Sum.inr 5216, 4), (Sum.inr 5232, 4), (Sum.inr 5264, 4), (Sum.inr 5339, 4), (Sum.inr 5381, 4), (Sum.inr 5382, 4), (Sum.inr 5385, 4), (Sum.inr 5402, 4), (Sum.inr 5436, 4), (Sum.inr 5446, 4)]

def numericRow2065 : Integer.Sparse Master := [(Sum.inr 2145, 1), (Sum.inr 2146, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2251, 1), (Sum.inr 2654, 1), (Sum.inr 2659, 1), (Sum.inr 2677, 1), (Sum.inr 2729, 1), (Sum.inr 3462, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3564, 1), (Sum.inr 3760, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3799, 1), (Sum.inr 3802, 1), (Sum.inr 3813, 1), (Sum.inr 3834, 1), (Sum.inr 3850, 1), (Sum.inr 3854, 1), (Sum.inr 3866, 1), (Sum.inr 3868, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1)]

def numericRow2066 : Integer.Sparse Master := [(Sum.inl 0, 723), (Sum.inl 5, -60), (Sum.inl 2, 75), (Sum.inl 7, -240), (Sum.inl 3, -1200), (Sum.inl 23, 720), (Sum.inl 12, -960), (Sum.inl 4, -480), (Sum.inl 27, 180), (Sum.inl 1, -540), (Sum.inr 1786, -12960), (Sum.inr 1787, -25920), (Sum.inr 1805, -12960), (Sum.inr 1982, -12960), (Sum.inr 1983, -25920), (Sum.inr 2046, -12960), (Sum.inr 2077, -12960), (Sum.inr 2150, -12960), (Sum.inr 2412, -12960), (Sum.inr 2419, -12960), (Sum.inr 2488, -25920), (Sum.inr 2796, -25920), (Sum.inr 2809, -12960), (Sum.inr 3425, -12960), (Sum.inr 3426, -12960), (Sum.inr 3478, -25920), (Sum.inr 3587, -12960), (Sum.inr 3589, -25920), (Sum.inr 3668, -25920), (Sum.inr 3677, -25920), (Sum.inr 3693, -25920), (Sum.inr 3701, -12960), (Sum.inr 3719, -25920), (Sum.inr 3751, -12960), (Sum.inr 3770, -25920), (Sum.inr 3795, -25920), (Sum.inr 3849, -12960), (Sum.inr 3857, -25920), (Sum.inr 3875, -12960), (Sum.inr 3876, -25920), (Sum.inr 3890, -12960), (Sum.inr 3892, -25920), (Sum.inr 3900, -12960), (Sum.inr 3901, -12960), (Sum.inr 3903, -25920), (Sum.inr 3964, -12960)]

def numericRow2067 : Integer.Sparse Master := [(Sum.inr 2556, -1), (Sum.inr 2896, -1), (Sum.inr 3521, -1), (Sum.inr 3597, -1), (Sum.inr 3709, -2), (Sum.inr 3721, -2), (Sum.inr 3731, -1), (Sum.inr 3792, -2), (Sum.inr 3836, -2), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 3867, -1), (Sum.inr 3900, -1), (Sum.inr 3909, -1), (Sum.inr 3964, -1), (Sum.inr 4025, -1), (Sum.inr 4663, 4), (Sum.inr 4666, 8), (Sum.inr 4677, 4), (Sum.inr 4851, 4), (Sum.inr 4956, 4), (Sum.inr 4958, 8), (Sum.inr 4964, 4), (Sum.inr 5129, 8), (Sum.inr 5377, 8), (Sum.inr 5379, 8), (Sum.inr 5430, 8)]

def numericRow2068 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2142, 1), (Sum.inr 2148, 2), (Sum.inr 2240, 1), (Sum.inr 3510, 1), (Sum.inr 3511, 2), (Sum.inr 3516, 2), (Sum.inr 3521, 1), (Sum.inr 3554, 1), (Sum.inr 3597, 1), (Sum.inr 3792, 2), (Sum.inr 3832, 2), (Sum.inr 3835, 2), (Sum.inr 3836, 2), (Sum.inr 3843, 2), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3900, 1), (Sum.inr 3909, 1)]

def numericRow2069 : Integer.Sparse Master := [(Sum.inr 2431, -1), (Sum.inr 2488, -1), (Sum.inr 2553, -1), (Sum.inr 3453, -1), (Sum.inr 3478, -1), (Sum.inr 3514, -1), (Sum.inr 3671, -1), (Sum.inr 3693, -1), (Sum.inr 3708, -1), (Sum.inr 3732, -1), (Sum.inr 3754, -1), (Sum.inr 3770, -1), (Sum.inr 3782, -1), (Sum.inr 3791, -1), (Sum.inr 3796, -1), (Sum.inr 3809, -1), (Sum.inr 3811, -1), (Sum.inr 3813, -1), (Sum.inr 3837, -2), (Sum.inr 3838, -1), (Sum.inr 3843, -1), (Sum.inr 4664, 4), (Sum.inr 4665, 4), (Sum.inr 4668, 4), (Sum.inr 4680, 4), (Sum.inr 4852, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4957, 4), (Sum.inr 4963, 4), (Sum.inr 5129, 4), (Sum.inr 5376, 4), (Sum.inr 5379, 4), (Sum.inr 5381, 8), (Sum.inr 5382, 4), (Sum.inr 5425, 4), (Sum.inr 5445, 4)]

def numericRow2070 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2145, 1), (Sum.inr 2147, 1), (Sum.inr 2154, 1), (Sum.inr 2250, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3478, 1), (Sum.inr 3508, 1), (Sum.inr 3509, 1), (Sum.inr 3514, 1), (Sum.inr 3516, 1), (Sum.inr 3553, 1), (Sum.inr 3754, 1), (Sum.inr 3770, 1), (Sum.inr 3791, 1), (Sum.inr 3796, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1), (Sum.inr 3832, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3840, 1), (Sum.inr 3866, 1), (Sum.inr 3880, 1)]

def numericRow2071 : Integer.Sparse Master := [(Sum.inr 1805, -1), (Sum.inr 1812, -1), (Sum.inr 1815, -2), (Sum.inr 2150, -1), (Sum.inr 2165, -1), (Sum.inr 2166, -2), (Sum.inr 2671, -1), (Sum.inr 2684, -2), (Sum.inr 2703, -1), (Sum.inr 2739, -2), (Sum.inr 3053, -1), (Sum.inr 3390, -1), (Sum.inr 3394, -2), (Sum.inr 3496, -1), (Sum.inr 3534, -2), (Sum.inr 3619, -1), (Sum.inr 4696, 4), (Sum.inr 4697, 4), (Sum.inr 4701, 8), (Sum.inr 4879, 4), (Sum.inr 5116, 4), (Sum.inr 5151, 8), (Sum.inr 5217, 8), (Sum.inr 5226, 8), (Sum.inr 5236, 8), (Sum.inr 5286, 4), (Sum.inr 5299, 8)]

def numericRow2072 : Integer.Sparse Master := [(Sum.inr 2150, 1), (Sum.inr 2165, 1), (Sum.inr 2166, 2), (Sum.inr 2238, 1), (Sum.inr 2239, 1), (Sum.inr 2246, 1), (Sum.inr 2257, 2), (Sum.inr 2655, 1), (Sum.inr 2656, 2), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2681, 2), (Sum.inr 2682, 2), (Sum.inr 2684, 2), (Sum.inr 2703, 1), (Sum.inr 2739, 2), (Sum.inr 3023, 1), (Sum.inr 3051, 2), (Sum.inr 3053, 1)]

def numericRow2073 : Integer.Sparse Master := [(Sum.inr 1802, -1), (Sum.inr 1807, -1), (Sum.inr 1810, -1), (Sum.inr 1814, -1), (Sum.inr 2141, -1), (Sum.inr 2151, -1), (Sum.inr 2152, -1), (Sum.inr 2157, -1), (Sum.inr 2522, -1), (Sum.inr 2672, -1), (Sum.inr 2685, -1), (Sum.inr 2686, -1), (Sum.inr 2694, -1), (Sum.inr 2722, -1), (Sum.inr 2723, -1), (Sum.inr 3054, -1), (Sum.inr 3391, -1), (Sum.inr 3397, -1), (Sum.inr 3493, -1), (Sum.inr 3533, -1), (Sum.inr 3544, -1), (Sum.inr 3626, -1), (Sum.inr 4698, 4), (Sum.inr 4699, 4), (Sum.inr 4700, 4), (Sum.inr 4703, 4), (Sum.inr 4880, 4), (Sum.inr 5035, 4), (Sum.inr 5140, 4), (Sum.inr 5215, 4), (Sum.inr 5216, 4), (Sum.inr 5219, 4), (Sum.inr 5220, 4), (Sum.inr 5229, 4), (Sum.inr 5232, 4), (Sum.inr 5233, 4), (Sum.inr 5254, 4), (Sum.inr 5266, 4), (Sum.inr 5267, 4)]

def numericRow2074 : Integer.Sparse Master := [(Sum.inr 2141, 1), (Sum.inr 2151, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2248, 1), (Sum.inr 2249, 1), (Sum.inr 2254, 1), (Sum.inr 2256, 1), (Sum.inr 2272, 1), (Sum.inr 2652, 1), (Sum.inr 2653, 1), (Sum.inr 2654, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2694, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 3016, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3054, 1)]

def numericRow2075 : Integer.Sparse Master := [(Sum.inl 0, 198), (Sum.inl 5, -30), (Sum.inl 8, -120), (Sum.inl 24, 360), (Sum.inl 27, 90), (Sum.inl 1, -210), (Sum.inr 2338, -3240), (Sum.inr 2339, -3240), (Sum.inr 2341, -6480), (Sum.inr 3416, -3240), (Sum.inr 3417, -6480), (Sum.inr 3420, -3240), (Sum.inr 3613, -3240), (Sum.inr 3616, -3240), (Sum.inr 3709, -3240), (Sum.inr 3790, -3240), (Sum.inr 3792, -3240), (Sum.inr 3815, -3240), (Sum.inr 3894, -3240), (Sum.inr 3896, -3240), (Sum.inr 3898, -3240), (Sum.inr 4010, -3240)]

def numericRow2076 : Integer.Sparse Master := [(Sum.inl 0, 54), (Sum.inl 5, -6), (Sum.inl 8, -24), (Sum.inl 24, 72), (Sum.inl 27, 18), (Sum.inl 1, 30), (Sum.inr 1967, -432), (Sum.inr 1969, -864), (Sum.inr 2029, -864), (Sum.inr 2183, -432), (Sum.inr 2185, -864), (Sum.inr 2225, -864), (Sum.inr 2330, -864), (Sum.inr 2337, -1728), (Sum.inr 3404, -864), (Sum.inr 3412, -1728), (Sum.inr 3603, -864), (Sum.inr 3672, -864), (Sum.inr 3694, -864), (Sum.inr 3756, -864), (Sum.inr 3773, -864), (Sum.inr 3779, -864), (Sum.inr 3797, -864), (Sum.inr 3896, -864), (Sum.inr 3903, -1728), (Sum.inr 4041, -432), (Sum.inr 4042, -864)]

def numericRow2077 : Integer.Sparse Master := [(Sum.inl 0, 984), (Sum.inl 5, -120), (Sum.inl 8, -480), (Sum.inl 27, 360), (Sum.inl 1, 120), (Sum.inl 30, 1440), (Sum.inr 2332, -12960), (Sum.inr 2334, -12960), (Sum.inr 2337, -12960), (Sum.inr 2342, -12960), (Sum.inr 2432, -6480), (Sum.inr 2489, -6480), (Sum.inr 3410, -12960), (Sum.inr 3411, -12960), (Sum.inr 3412, -12960), (Sum.inr 3421, -12960), (Sum.inr 3456, -6480), (Sum.inr 3482, -6480), (Sum.inr 3607, -12960), (Sum.inr 3616, -6480), (Sum.inr 3672, -6480), (Sum.inr 3694, -6480), (Sum.inr 3756, -6480), (Sum.inr 3773, -6480), (Sum.inr 3898, -6480), (Sum.inr 4041, -6480), (Sum.inr 4042, -12960), (Sum.inr 4043, -6480), (Sum.inr 4045, -12960), (Sum.inr 4047, -12960)]

def numericRow2078 : Integer.Sparse Master := [(Sum.inr 2489, -1), (Sum.inr 2954, -2), (Sum.inr 3482, -1), (Sum.inr 3606, -2), (Sum.inr 3694, -1), (Sum.inr 3773, -1), (Sum.inr 3779, -1), (Sum.inr 3787, -2), (Sum.inr 3797, -1), (Sum.inr 3804, -2), (Sum.inr 3857, -2), (Sum.inr 3876, -2), (Sum.inr 3983, -4), (Sum.inr 4942, 8), (Sum.inr 4944, 8), (Sum.inr 4945, 8), (Sum.inr 4951, 8), (Sum.inr 5043, 4), (Sum.inr 5189, 4), (Sum.inr 5217, 4), (Sum.inr 5236, 4), (Sum.inr 5269, 4), (Sum.inr 5340, 4), (Sum.inr 5419, 4), (Sum.inr 5461, 4), (Sum.inr 5463, 4)]

def numericRow2079 : Integer.Sparse Master := [(Sum.inr 2656, 1), (Sum.inr 2658, 2), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 3407, 2), (Sum.inr 3413, 2), (Sum.inr 3418, 2), (Sum.inr 3465, 1), (Sum.inr 3482, 1), (Sum.inr 3542, 1), (Sum.inr 3606, 2), (Sum.inr 3763, 1), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3804, 2), (Sum.inr 3842, 1), (Sum.inr 3857, 2), (Sum.inr 3960, 1), (Sum.inr 3973, 1), (Sum.inr 3983, 2)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow208 : Integer.Sparse Master := [(Sum.inr 2603, 1), (Sum.inr 3050, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def numericRow209 : Integer.Sparse Master := [(Sum.inr 1374, 1), (Sum.inr 2888, 1), (Sum.inr 2978, 2), (Sum.inr 3052, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

def numericRow210 : Integer.Sparse Master := [(Sum.inr 2035, 1), (Sum.inr 2597, 1), (Sum.inr 2973, 1), (Sum.inr 2978, 1), (Sum.inr 3052, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

def numericRow211 : Integer.Sparse Master := [(Sum.inr 3052, 1), (Sum.inr 3540, 2), (Sum.inr 3548, 1), (Sum.inr 3582, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def numericRow212 : Integer.Sparse Master := [(Sum.inr 2062, 1), (Sum.inr 2879, 2), (Sum.inr 2888, 1), (Sum.inr 3052, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def numericRow213 : Integer.Sparse Master := [(Sum.inl 0, -772), (Sum.inl 5, 160), (Sum.inl 6, 20), (Sum.inl 2, -540), (Sum.inl 7, -640), (Sum.inl 35, -640), (Sum.inl 3, -3200), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -1280), (Sum.inl 4, -1280), (Sum.inl 1, 1220), (Sum.inr 1210, 17280), (Sum.inr 1211, 17280), (Sum.inr 1219, 17280), (Sum.inr 1230, 17280), (Sum.inr 1261, 17280), (Sum.inr 2071, 17280), (Sum.inr 2080, 17280), (Sum.inr 2090, 17280), (Sum.inr 2197, 17280), (Sum.inr 2860, 17280), (Sum.inr 2867, 17280), (Sum.inr 2876, 17280), (Sum.inr 2916, 17280), (Sum.inr 2922, 17280), (Sum.inr 2933, 17280), (Sum.inr 2984, 17280), (Sum.inr 3016, 17280), (Sum.inr 3025, 17280), (Sum.inr 3038, 17280), (Sum.inr 3097, 17280), (Sum.inr 3814, 17280), (Sum.inr 3872, 17280), (Sum.inr 3877, 17280)]

def numericRow214 : Integer.Sparse Master := [(Sum.inl 0, -66), (Sum.inl 2, -45), (Sum.inl 3, -240), (Sum.inl 13, -160), (Sum.inl 4, -80), (Sum.inl 1, -15), (Sum.inr 2043, 4320), (Sum.inr 2045, 4320), (Sum.inr 2049, 4320), (Sum.inr 2055, 4320), (Sum.inr 2259, 4320), (Sum.inr 3285, 4320), (Sum.inr 3287, 4320), (Sum.inr 3295, 4320), (Sum.inr 3296, 4320), (Sum.inr 3463, 4320), (Sum.inr 3478, 4320), (Sum.inr 3479, 4320), (Sum.inr 3516, 4320), (Sum.inr 3517, 4320), (Sum.inr 3527, 4320), (Sum.inr 3528, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3538, 4320), (Sum.inr 3541, 4320), (Sum.inr 3560, 4320), (Sum.inr 3572, 4320), (Sum.inr 3575, 4320), (Sum.inr 3577, 4320), (Sum.inr 3813, 4320), (Sum.inr 3840, 4320), (Sum.inr 3854, 4320)]

def numericRow215 : Integer.Sparse Master := [(Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

def numericRow216 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 1218, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1263, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def numericRow217 : Integer.Sparse Master := [(Sum.inr 1263, 1), (Sum.inr 2568, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 2758, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

def numericRow218 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

def numericRow219 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 2481, 1), (Sum.inr 2616, 1), (Sum.inr 2714, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def numericRow220 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2568, 1), (Sum.inr 2724, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

def numericRow221 : Integer.Sparse Master := [(Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

def numericRow222 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2619, 1), (Sum.inr 2620, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

def numericRow223 : Integer.Sparse Master := [(Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 2620, 1), (Sum.inr 2722, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2080 : Integer.Sparse Master := [(Sum.inr 2432, -1), (Sum.inr 2489, -1), (Sum.inr 2924, -2), (Sum.inr 3456, -1), (Sum.inr 3482, -1), (Sum.inr 3605, -2), (Sum.inr 3672, -1), (Sum.inr 3694, -1), (Sum.inr 3709, -1), (Sum.inr 3756, -1), (Sum.inr 3773, -1), (Sum.inr 3790, -1), (Sum.inr 3792, -1), (Sum.inr 3815, -1), (Sum.inr 3838, -2), (Sum.inr 3843, -2), (Sum.inr 3974, -4), (Sum.inr 4930, 8), (Sum.inr 4931, 8), (Sum.inr 4933, 8), (Sum.inr 4942, 8), (Sum.inr 5377, 4), (Sum.inr 5419, 8), (Sum.inr 5461, 4)]

def numericRow2081 : Integer.Sparse Master := [(Sum.inr 3406, 2), (Sum.inr 3407, 2), (Sum.inr 3408, 2), (Sum.inr 3414, 2), (Sum.inr 3456, 1), (Sum.inr 3482, 1), (Sum.inr 3605, 2), (Sum.inr 3756, 1), (Sum.inr 3773, 1), (Sum.inr 3792, 1), (Sum.inr 3815, 1), (Sum.inr 3835, 1), (Sum.inr 3842, 2), (Sum.inr 3843, 2), (Sum.inr 3973, 1), (Sum.inr 3974, 2)]

def numericRow2082 : Integer.Sparse Master := [(Sum.inr 2338, -1), (Sum.inr 2483, -1), (Sum.inr 2814, -1), (Sum.inr 3416, -1), (Sum.inr 3477, -1), (Sum.inr 3585, -1), (Sum.inr 3690, -2), (Sum.inr 3692, -2), (Sum.inr 3764, -2), (Sum.inr 3769, -2), (Sum.inr 3789, -1), (Sum.inr 3801, -2), (Sum.inr 3810, -1), (Sum.inr 3812, -2), (Sum.inr 3957, -2), (Sum.inr 4756, 4), (Sum.inr 4757, 4), (Sum.inr 4768, 4), (Sum.inr 4795, 8), (Sum.inr 4933, 8), (Sum.inr 4955, 8), (Sum.inr 5184, 4), (Sum.inr 5338, 8), (Sum.inr 5348, 8), (Sum.inr 5414, 4), (Sum.inr 5429, 8)]

def numericRow2083 : Integer.Sparse Master := [(Sum.inr 2176, 1), (Sum.inr 2178, 1), (Sum.inr 2181, 1), (Sum.inr 2213, 2), (Sum.inr 3414, 2), (Sum.inr 3416, 1), (Sum.inr 3477, 1), (Sum.inr 3508, 2), (Sum.inr 3524, 1), (Sum.inr 3585, 1), (Sum.inr 3755, 2), (Sum.inr 3764, 2), (Sum.inr 3768, 2), (Sum.inr 3769, 2), (Sum.inr 3810, 1), (Sum.inr 3812, 2), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3957, 1)]

def numericRow2084 : Integer.Sparse Master := [(Sum.inr 2332, -1), (Sum.inr 2480, -1), (Sum.inr 2809, -1), (Sum.inr 2931, -1), (Sum.inr 3410, -1), (Sum.inr 3467, -1), (Sum.inr 3587, -1), (Sum.inr 3612, -1), (Sum.inr 3690, -2), (Sum.inr 3692, -1), (Sum.inr 3694, -1), (Sum.inr 3764, -2), (Sum.inr 3769, -1), (Sum.inr 3773, -1), (Sum.inr 3787, -1), (Sum.inr 3800, -1), (Sum.inr 3804, -1), (Sum.inr 3805, -1), (Sum.inr 3957, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4930, 4), (Sum.inr 4933, 4), (Sum.inr 4954, 4), (Sum.inr 4955, 4), (Sum.inr 4958, 4), (Sum.inr 5040, 4), (Sum.inr 5067, 4), (Sum.inr 5185, 4), (Sum.inr 5338, 4), (Sum.inr 5340, 4), (Sum.inr 5348, 4), (Sum.inr 5470, 4)]

def numericRow2085 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3467, 1), (Sum.inr 3476, 1), (Sum.inr 3508, 1), (Sum.inr 3511, 1), (Sum.inr 3529, 1), (Sum.inr 3587, 1), (Sum.inr 3612, 1), (Sum.inr 3755, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 1), (Sum.inr 3773, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3955, 1), (Sum.inr 3957, 1), (Sum.inr 3961, 1)]

def numericRow2086 : Integer.Sparse Master := [(Sum.inr 2330, -1), (Sum.inr 2479, -1), (Sum.inr 2561, -2), (Sum.inr 2807, -1), (Sum.inr 3404, -1), (Sum.inr 3459, -1), (Sum.inr 3522, -2), (Sum.inr 3590, -1), (Sum.inr 3693, -2), (Sum.inr 3703, -1), (Sum.inr 3758, -1), (Sum.inr 3770, -2), (Sum.inr 3786, -1), (Sum.inr 3799, -1), (Sum.inr 3800, -1), (Sum.inr 3805, -1), (Sum.inr 3845, -4), (Sum.inr 4931, 8), (Sum.inr 4956, 4), (Sum.inr 4957, 8), (Sum.inr 5112, 4), (Sum.inr 5187, 4), (Sum.inr 5339, 8), (Sum.inr 5353, 8), (Sum.inr 5414, 4)]

def numericRow2087 : Integer.Sparse Master := [(Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3459, 1), (Sum.inr 3509, 2), (Sum.inr 3510, 1), (Sum.inr 3522, 2), (Sum.inr 3537, 1), (Sum.inr 3556, 1), (Sum.inr 3590, 1), (Sum.inr 3758, 1), (Sum.inr 3760, 2), (Sum.inr 3761, 2), (Sum.inr 3770, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3845, 2), (Sum.inr 3869, 1)]

def numericRow2088 : Integer.Sparse Master := [(Sum.inr 2341, -1), (Sum.inr 2515, -1), (Sum.inr 2817, -1), (Sum.inr 3417, -1), (Sum.inr 3479, -1), (Sum.inr 3591, -1), (Sum.inr 3671, -1), (Sum.inr 3693, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3754, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3770, -1), (Sum.inr 3782, -1), (Sum.inr 3796, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3814, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4775, 4), (Sum.inr 4776, 4), (Sum.inr 4777, 4), (Sum.inr 4821, 4), (Sum.inr 4856, 4), (Sum.inr 4942, 4), (Sum.inr 4951, 4), (Sum.inr 4963, 4), (Sum.inr 4966, 4), (Sum.inr 5198, 4), (Sum.inr 5338, 4), (Sum.inr 5353, 4), (Sum.inr 5360, 4), (Sum.inr 5361, 4), (Sum.inr 5421, 4), (Sum.inr 5436, 4), (Sum.inr 5446, 4)]

def numericRow2089 : Integer.Sparse Master := [(Sum.inr 2211, 1), (Sum.inr 2212, 1), (Sum.inr 2217, 1), (Sum.inr 2223, 1), (Sum.inr 2274, 1), (Sum.inr 3407, 1), (Sum.inr 3417, 1), (Sum.inr 3418, 1), (Sum.inr 3479, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3570, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3767, 1), (Sum.inr 3770, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3958, 1)]

def numericRow2090 : Integer.Sparse Master := [(Sum.inr 2337, -1), (Sum.inr 2512, -1), (Sum.inr 2813, -1), (Sum.inr 2889, -1), (Sum.inr 3412, -1), (Sum.inr 3471, -1), (Sum.inr 3595, -1), (Sum.inr 3631, -1), (Sum.inr 3670, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3706, -1), (Sum.inr 3753, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3771, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3809, -1), (Sum.inr 3813, -1), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 3963, -2), (Sum.inr 4944, 4), (Sum.inr 4951, 4), (Sum.inr 4964, 4), (Sum.inr 4965, 4), (Sum.inr 4966, 4), (Sum.inr 5044, 4), (Sum.inr 5090, 4), (Sum.inr 5199, 4), (Sum.inr 5338, 4), (Sum.inr 5359, 4), (Sum.inr 5361, 4), (Sum.inr 5446, 4)]

def numericRow2091 : Integer.Sparse Master := [(Sum.inr 3412, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3471, 1), (Sum.inr 3474, 1), (Sum.inr 3475, 1), (Sum.inr 3480, 1), (Sum.inr 3554, 1), (Sum.inr 3555, 1), (Sum.inr 3578, 1), (Sum.inr 3595, 1), (Sum.inr 3631, 1), (Sum.inr 3753, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3767, 1), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3958, 1), (Sum.inr 3959, 1), (Sum.inr 3963, 1)]

def numericRow2092 : Integer.Sparse Master := [(Sum.inr 2332, -1), (Sum.inr 2339, -1), (Sum.inr 2342, -2), (Sum.inr 2809, -1), (Sum.inr 2815, -1), (Sum.inr 2818, -2), (Sum.inr 2884, -1), (Sum.inr 2893, -1), (Sum.inr 2931, -2), (Sum.inr 3410, -1), (Sum.inr 3420, -1), (Sum.inr 3421, -2), (Sum.inr 3587, -1), (Sum.inr 3588, -1), (Sum.inr 3592, -2), (Sum.inr 3599, -1), (Sum.inr 3612, -2), (Sum.inr 3621, -1), (Sum.inr 3672, -2), (Sum.inr 3690, -2), (Sum.inr 3694, -2), (Sum.inr 3756, -2), (Sum.inr 3764, -2), (Sum.inr 3773, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 3958, -2), (Sum.inr 3961, -2), (Sum.inr 4091, 4)]

def numericRow2093 : Integer.Sparse Master := [(Sum.inr 2330, -1), (Sum.inr 2334, -1), (Sum.inr 2337, -1), (Sum.inr 2341, -1), (Sum.inr 2428, -1), (Sum.inr 2434, -1), (Sum.inr 2561, -1), (Sum.inr 2807, -1), (Sum.inr 2813, -1), (Sum.inr 2817, -1), (Sum.inr 2881, -1), (Sum.inr 3404, -1), (Sum.inr 3411, -1), (Sum.inr 3412, -1), (Sum.inr 3417, -1), (Sum.inr 3450, -1), (Sum.inr 3457, -1), (Sum.inr 3522, -1), (Sum.inr 3590, -1), (Sum.inr 3591, -1), (Sum.inr 3595, -1), (Sum.inr 3624, -1), (Sum.inr 3670, -1), (Sum.inr 3671, -1), (Sum.inr 3689, -1), (Sum.inr 3693, -1), (Sum.inr 3703, -1), (Sum.inr 3705, -1), (Sum.inr 3706, -1), (Sum.inr 3753, -1), (Sum.inr 3754, -1), (Sum.inr 3757, -1), (Sum.inr 3758, -1), (Sum.inr 3767, -1), (Sum.inr 3770, -1), (Sum.inr 3771, -1), (Sum.inr 3781, -1), (Sum.inr 3794, -1), (Sum.inr 3845, -2), (Sum.inr 3958, -1), (Sum.inr 3961, -1), (Sum.inr 4092, 4)]

def numericRow2094 : Integer.Sparse Master := [(Sum.inr 1963, -1), (Sum.inr 1969, -1), (Sum.inr 1970, -1), (Sum.inr 2174, -1), (Sum.inr 2185, -1), (Sum.inr 2186, -1), (Sum.inr 2509, -1), (Sum.inr 2686, -2), (Sum.inr 2694, -1), (Sum.inr 2704, -1), (Sum.inr 2705, -2), (Sum.inr 2743, -2), (Sum.inr 3077, -1), (Sum.inr 3397, -2), (Sum.inr 3493, -1), (Sum.inr 3498, -2), (Sum.inr 3548, -2), (Sum.inr 3625, -1), (Sum.inr 4945, 8), (Sum.inr 4975, 4), (Sum.inr 4976, 8), (Sum.inr 5205, 4), (Sum.inr 5215, 8), (Sum.inr 5277, 4), (Sum.inr 5282, 4), (Sum.inr 5287, 8)]

def numericRow2095 : Integer.Sparse Master := [(Sum.inr 2174, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2653, 2), (Sum.inr 2658, 2), (Sum.inr 2659, 2), (Sum.inr 2686, 2), (Sum.inr 2690, 1), (Sum.inr 2694, 1), (Sum.inr 2704, 1), (Sum.inr 2705, 2), (Sum.inr 2706, 1), (Sum.inr 2743, 2), (Sum.inr 3025, 2), (Sum.inr 3059, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2096 : Integer.Sparse Master := [(Sum.inr 2317, -1), (Sum.inr 2318, -2), (Sum.inr 2328, -1), (Sum.inr 2412, -1), (Sum.inr 2452, -2), (Sum.inr 2796, -2), (Sum.inr 2804, -1), (Sum.inr 2853, -1), (Sum.inr 3399, -1), (Sum.inr 3400, -2), (Sum.inr 3401, -1), (Sum.inr 3426, -1), (Sum.inr 3433, -2), (Sum.inr 3586, -1), (Sum.inr 3589, -2), (Sum.inr 3620, -1), (Sum.inr 3678, -2), (Sum.inr 3683, -2), (Sum.inr 3687, -2), (Sum.inr 3701, -1), (Sum.inr 3744, -2), (Sum.inr 3746, -2), (Sum.inr 3749, -2), (Sum.inr 3751, -1), (Sum.inr 3781, -2), (Sum.inr 3794, -2), (Sum.inr 3945, -1), (Sum.inr 3952, -1), (Sum.inr 4090, 4)]

def numericRow2097 : Integer.Sparse Master := [(Sum.inr 2371, -1), (Sum.inr 2372, -2), (Sum.inr 2419, -1), (Sum.inr 2459, -2), (Sum.inr 2536, -1), (Sum.inr 3335, -1), (Sum.inr 3336, -2), (Sum.inr 3370, -1), (Sum.inr 3425, -1), (Sum.inr 3429, -2), (Sum.inr 3668, -2), (Sum.inr 3677, -2), (Sum.inr 3681, -4), (Sum.inr 3683, -2), (Sum.inr 3713, -2), (Sum.inr 3719, -2), (Sum.inr 3721, -1), (Sum.inr 3746, -2), (Sum.inr 3776, -1), (Sum.inr 3778, -1), (Sum.inr 3779, -2), (Sum.inr 3795, -2), (Sum.inr 3797, -2), (Sum.inr 3836, -1), (Sum.inr 4088, 4)]

def numericRow2098 : Integer.Sparse Master := [(Sum.inr 4073, 2), (Sum.inr 4074, 2), (Sum.inr 4075, 4), (Sum.inr 4078, 1), (Sum.inr 4080, 2), (Sum.inr 4082, 2), (Sum.inr 4086, 2), (Sum.inr 4087, 1), (Sum.inr 4088, 4), (Sum.inr 4089, 2), (Sum.inr 4090, 2), (Sum.inr 4091, 2), (Sum.inr 4092, 4)]

def numericRow2099 : Integer.Sparse Master := [(Sum.inl 0, 189), (Sum.inl 5, 60), (Sum.inl 2, -45), (Sum.inl 7, 240), (Sum.inl 3, 720), (Sum.inl 23, -720), (Sum.inl 12, 480), (Sum.inl 27, -180), (Sum.inl 1, 930), (Sum.inr 1798, -12960), (Sum.inr 1811, -4320), (Sum.inr 2067, -12960), (Sum.inr 2100, -8640), (Sum.inr 2156, -4320), (Sum.inr 2804, -12960), (Sum.inr 2814, -4320), (Sum.inr 3585, -4320), (Sum.inr 3586, -12960), (Sum.inr 3713, -25920), (Sum.inr 3731, -4320), (Sum.inr 3732, -25920), (Sum.inr 3811, -25920), (Sum.inr 3867, -4320), (Sum.inr 3885, -25920), (Sum.inr 3891, -12960), (Sum.inr 3899, -8640), (Sum.inr 3902, -12960)]

def numericRow2100 : Integer.Sparse Master := [(Sum.inr 2589, -1), (Sum.inr 3563, -1), (Sum.inr 3721, -3), (Sum.inr 3836, -3), (Sum.inr 3849, -3), (Sum.inr 3875, -3), (Sum.inr 3909, -1), (Sum.inr 4025, -1), (Sum.inr 4675, 4), (Sum.inr 4677, 12), (Sum.inr 4863, 4), (Sum.inr 4964, 12), (Sum.inr 4975, 4), (Sum.inr 5243, 12), (Sum.inr 5379, 24), (Sum.inr 5429, 12)]

def numericRow2101 : Integer.Sparse Master := [(Sum.inr 2139, 1), (Sum.inr 2142, 3), (Sum.inr 2232, 1), (Sum.inr 2690, 1), (Sum.inr 2697, 3), (Sum.inr 3554, 3), (Sum.inr 3563, 1), (Sum.inr 3832, 6), (Sum.inr 3836, 3), (Sum.inr 3846, 3), (Sum.inr 3875, 3), (Sum.inr 3909, 1)]

def numericRow2102 : Integer.Sparse Master := [(Sum.inl 0, 391), (Sum.inl 5, 120), (Sum.inl 6, 15), (Sum.inl 2, -280), (Sum.inl 7, 400), (Sum.inl 8, -160), (Sum.inl 3, 640), (Sum.inl 23, -480), (Sum.inl 24, -960), (Sum.inl 4, 320), (Sum.inl 27, -360), (Sum.inl 1, -270), (Sum.inr 1802, -8640), (Sum.inr 1805, -8640), (Sum.inr 2105, -4320), (Sum.inr 2141, -8640), (Sum.inr 2150, -8640), (Sum.inr 2241, -4320), (Sum.inr 2807, -8640), (Sum.inr 2809, -8640), (Sum.inr 3587, -8640), (Sum.inr 3590, -8640), (Sum.inr 3602, -4320), (Sum.inr 3719, -17280), (Sum.inr 3721, -8640), (Sum.inr 3795, -17280), (Sum.inr 3836, -8640), (Sum.inr 3849, -8640), (Sum.inr 3875, -8640), (Sum.inr 3891, -8640), (Sum.inr 3892, -17280), (Sum.inr 3901, -8640), (Sum.inr 3910, -8640)]

def numericRow2103 : Integer.Sparse Master := [(Sum.inr 1805, -3), (Sum.inr 1811, -1), (Sum.inr 2150, -3), (Sum.inr 2156, -1), (Sum.inr 2684, -3), (Sum.inr 2721, -3), (Sum.inr 3053, -1), (Sum.inr 3394, -3), (Sum.inr 3532, -3), (Sum.inr 3619, -1), (Sum.inr 4695, 4), (Sum.inr 4696, 12), (Sum.inr 4878, 4), (Sum.inr 5226, 24), (Sum.inr 5231, 12), (Sum.inr 5265, 12)]

def numericRow2104 : Integer.Sparse Master := [(Sum.inr 2150, 3), (Sum.inr 2156, 1), (Sum.inr 2231, 1), (Sum.inr 2234, 1), (Sum.inr 2238, 3), (Sum.inr 2669, 6), (Sum.inr 2676, 3), (Sum.inr 2684, 3), (Sum.inr 2721, 3), (Sum.inr 3037, 3), (Sum.inr 3053, 1)]

def numericRow2105 : Integer.Sparse Master := [(Sum.inl 0, 319), (Sum.inl 5, 60), (Sum.inl 6, 15), (Sum.inl 2, -220), (Sum.inl 7, -80), (Sum.inl 8, 80), (Sum.inl 3, -320), (Sum.inl 24, -240), (Sum.inl 4, -320), (Sum.inl 27, -180), (Sum.inl 1, 430), (Sum.inl 30, -480), (Sum.inr 2330, -8640), (Sum.inr 2332, -8640), (Sum.inr 3404, -8640), (Sum.inr 3410, -8640), (Sum.inr 3602, -4320), (Sum.inr 3779, -8640), (Sum.inr 3797, -8640), (Sum.inr 3898, -4320), (Sum.inr 4042, -8640), (Sum.inr 4046, -8640)]

def numericRow2106 : Integer.Sparse Master := [(Sum.inr 4073, 8), (Sum.inr 4079, 2), (Sum.inr 4088, 12), (Sum.inr 4091, 8)]

def numericRow2107 : Integer.Sparse Master := [(Sum.inl 0, 303), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, -60), (Sum.inl 7, 480), (Sum.inl 3, 960), (Sum.inl 23, -720), (Sum.inl 12, 480), (Sum.inl 27, -180), (Sum.inl 1, 1500), (Sum.inr 2896, -12960), (Sum.inr 3597, -12960), (Sum.inr 3603, -12960), (Sum.inr 3708, -12960), (Sum.inr 3789, -12960), (Sum.inr 3791, -12960), (Sum.inr 3810, -12960), (Sum.inr 3891, -12960), (Sum.inr 3902, -12960)]

def numericRow2108 : Integer.Sparse Master := [(Sum.inl 0, 225), (Sum.inl 5, -60), (Sum.inl 6, 15), (Sum.inl 2, -270), (Sum.inl 7, -240), (Sum.inl 8, -240), (Sum.inl 3, -1440), (Sum.inl 24, 720), (Sum.inl 12, -480), (Sum.inl 4, -960), (Sum.inl 27, 180), (Sum.inl 1, 210), (Sum.inr 1959, -3240), (Sum.inr 1963, -12960), (Sum.inr 2019, -12960), (Sum.inr 2170, -3240), (Sum.inr 2174, -12960), (Sum.inr 2190, -12960), (Sum.inr 3670, -12960), (Sum.inr 3689, -12960), (Sum.inr 3753, -12960), (Sum.inr 3757, -12960), (Sum.inr 3837, -25920), (Sum.inr 3896, -12960), (Sum.inr 3901, -12960)]

def numericRow2109 : Integer.Sparse Master := [(Sum.inr 2483, -1), (Sum.inr 3477, -1), (Sum.inr 3692, -1), (Sum.inr 3769, -1), (Sum.inr 3787, -2), (Sum.inr 3801, -2), (Sum.inr 3804, -2), (Sum.inr 3812, -2), (Sum.inr 3849, -1), (Sum.inr 3875, -1), (Sum.inr 4761, 4), (Sum.inr 4762, 4), (Sum.inr 4768, 4), (Sum.inr 4803, 8), (Sum.inr 5044, 8), (Sum.inr 5187, 4), (Sum.inr 5215, 8), (Sum.inr 5219, 4), (Sum.inr 5249, 4), (Sum.inr 5338, 8), (Sum.inr 5353, 8), (Sum.inr 5414, 4), (Sum.inr 5425, 8), (Sum.inr 5430, 8)]

def numericRow2110 : Integer.Sparse Master := [(Sum.inr 2171, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2195, 2), (Sum.inr 2653, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 3474, 2), (Sum.inr 3477, 1), (Sum.inr 3537, 1), (Sum.inr 3755, 2), (Sum.inr 3761, 2), (Sum.inr 3769, 1), (Sum.inr 3804, 2), (Sum.inr 3812, 2), (Sum.inr 3840, 2), (Sum.inr 3849, 1), (Sum.inr 3869, 1), (Sum.inr 3871, 2)]

def numericRow2111 : Integer.Sparse Master := [(Sum.inr 4077, 1), (Sum.inr 4078, 4), (Sum.inr 4080, 4), (Sum.inr 4086, 4), (Sum.inr 4088, 4), (Sum.inr 4090, 4), (Sum.inr 4091, 4), (Sum.inr 4092, 4)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2113 : Integer.Sparse Master := [(Sum.inr 686, 4), (Sum.inr 1541, 1), (Sum.inr 4062, -1)]

def numericRow2114 : Integer.Sparse Master := [(Sum.inr 1521, 1), (Sum.inr 1532, 3), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 4060, -1)]

def numericRow2115 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1521, 1), (Sum.inr 1537, 2), (Sum.inr 4060, -1)]

def numericRow2116 : Integer.Sparse Master := [(Sum.inr 683, 3), (Sum.inr 695, 1), (Sum.inr 1537, 1), (Sum.inr 4060, -1)]

def numericRow2117 : Integer.Sparse Master := [(Sum.inr 1527, 1), (Sum.inr 1529, 3), (Sum.inr 1531, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def numericRow2118 : Integer.Sparse Master := [(Sum.inr 1523, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def numericRow2119 : Integer.Sparse Master := [(Sum.inr 1533, 3), (Sum.inr 1538, 2), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def numericRow2120 : Integer.Sparse Master := [(Sum.inr 1496, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

def numericRow2121 : Integer.Sparse Master := [(Sum.inr 1495, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 4061, -1)]

def numericRow2122 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1518, 2), (Sum.inr 1520, 1), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def numericRow2123 : Integer.Sparse Master := [(Sum.inr 1509, 1), (Sum.inr 1528, 2), (Sum.inr 1530, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def numericRow2124 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1509, 1), (Sum.inr 1518, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

def numericRow2125 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1513, 1), (Sum.inr 1519, 1), (Sum.inr 1525, 2), (Sum.inr 4059, -1)]

def numericRow2126 : Integer.Sparse Master := [(Sum.inr 1519, 1), (Sum.inr 1522, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

def numericRow2127 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1519, 2), (Sum.inr 1536, 2), (Sum.inr 4059, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2128 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1503, 1), (Sum.inr 1507, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

def numericRow2129 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1517, 3), (Sum.inr 4057, -1)]

def numericRow2130 : Integer.Sparse Master := [(Sum.inr 1507, 1), (Sum.inr 1510, 1), (Sum.inr 1512, 2), (Sum.inr 1517, 1), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

def numericRow2131 : Integer.Sparse Master := [(Sum.inr 1491, 1), (Sum.inr 1517, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

def numericRow2132 : Integer.Sparse Master := [(Sum.inr 1502, 2), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

def numericRow2133 : Integer.Sparse Master := [(Sum.inr 1497, 1), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

def numericRow2134 : Integer.Sparse Master := [(Sum.inr 1688, 2), (Sum.inr 1692, 2), (Sum.inr 1695, 2), (Sum.inr 4066, -1)]

def numericRow2135 : Integer.Sparse Master := [(Sum.inr 1692, 2), (Sum.inr 3262, 2), (Sum.inr 3275, 2), (Sum.inr 4066, -1)]

def numericRow2136 : Integer.Sparse Master := [(Sum.inr 1685, 2), (Sum.inr 1687, 1), (Sum.inr 1694, 1), (Sum.inr 1743, 1), (Sum.inr 2167, 1), (Sum.inr 4067, -1)]

def numericRow2137 : Integer.Sparse Master := [(Sum.inr 1679, 2), (Sum.inr 1683, 1), (Sum.inr 1693, 1), (Sum.inr 1735, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def numericRow2138 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1748, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

def numericRow2139 : Integer.Sparse Master := [(Sum.inr 1683, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2258, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def numericRow2140 : Integer.Sparse Master := [(Sum.inr 1694, 1), (Sum.inr 2167, 1), (Sum.inr 3268, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def numericRow2141 : Integer.Sparse Master := [(Sum.inr 1693, 1), (Sum.inr 3272, 2), (Sum.inr 3276, 2), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def numericRow2142 : Integer.Sparse Master := [(Sum.inr 3237, 1), (Sum.inr 3252, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

def numericRow2143 : Integer.Sparse Master := [(Sum.inr 1849, 2), (Sum.inr 1858, 1), (Sum.inr 2167, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2144 : Integer.Sparse Master := [(Sum.inr 1690, 1), (Sum.inr 2184, 1), (Sum.inr 3255, 1), (Sum.inr 3264, 2), (Sum.inr 3273, 1), (Sum.inr 4064, -1)]

def numericRow2145 : Integer.Sparse Master := [(Sum.inr 1681, 1), (Sum.inr 2657, 1), (Sum.inr 3258, 1), (Sum.inr 3265, 1), (Sum.inr 3270, 2), (Sum.inr 4065, -1)]

def numericRow2146 : Integer.Sparse Master := [(Sum.inr 1691, 1), (Sum.inr 3261, 1), (Sum.inr 3265, 2), (Sum.inr 3274, 2), (Sum.inr 4065, -1)]

def numericRow2147 : Integer.Sparse Master := [(Sum.inr 2161, 2), (Sum.inr 2163, 2), (Sum.inr 2169, 2), (Sum.inr 4076, -1)]

def numericRow2148 : Integer.Sparse Master := [(Sum.inr 2155, 2), (Sum.inr 2159, 1), (Sum.inr 2168, 1), (Sum.inr 2273, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

def numericRow2149 : Integer.Sparse Master := [(Sum.inr 2164, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2286, 1), (Sum.inr 3423, 1), (Sum.inr 4076, -1)]

def numericRow2150 : Integer.Sparse Master := [(Sum.inr 2168, 1), (Sum.inr 3415, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3596, 1), (Sum.inr 4076, -1)]

def numericRow2151 : Integer.Sparse Master := [(Sum.inr 3419, 2), (Sum.inr 3422, 2), (Sum.inr 3423, 2), (Sum.inr 4076, -1)]

def numericRow2152 : Integer.Sparse Master := [(Sum.inr 2169, 2), (Sum.inr 3423, 2), (Sum.inr 3512, 2), (Sum.inr 4076, -1)]

def numericRow2153 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2151, 1), (Sum.inr 2153, 1), (Sum.inr 2165, 1), (Sum.inr 2256, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

def numericRow2154 : Integer.Sparse Master := [(Sum.inr 2160, 1), (Sum.inr 2162, 2), (Sum.inr 2165, 1), (Sum.inr 2180, 1), (Sum.inr 2186, 1), (Sum.inr 4074, -1)]

def numericRow2155 : Integer.Sparse Master := [(Sum.inr 2140, 1), (Sum.inr 2143, 1), (Sum.inr 2151, 2), (Sum.inr 2239, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

def numericRow2156 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3411, 2), (Sum.inr 3413, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 1), (Sum.inr 4074, -1)]

def numericRow2157 : Integer.Sparse Master := [(Sum.inr 2181, 1), (Sum.inr 2185, 1), (Sum.inr 2186, 1), (Sum.inr 2223, 2), (Sum.inr 3420, 1), (Sum.inr 4074, -1)]

def numericRow2158 : Integer.Sparse Master := [(Sum.inr 2185, 1), (Sum.inr 3411, 2), (Sum.inr 3420, 1), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

def numericRow2159 : Integer.Sparse Master := [(Sum.inr 2143, 1), (Sum.inr 2176, 1), (Sum.inr 2185, 1), (Sum.inr 2212, 2), (Sum.inr 3588, 1), (Sum.inr 4074, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow2160 : Integer.Sparse Master := [(Sum.inr 2165, 1), (Sum.inr 2186, 1), (Sum.inr 3420, 1), (Sum.inr 3457, 2), (Sum.inr 3510, 1), (Sum.inr 4074, -1)]

def numericRow2161 : Integer.Sparse Master := [(Sum.inr 2144, 1), (Sum.inr 2146, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2249, 1), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

def numericRow2162 : Integer.Sparse Master := [(Sum.inr 2154, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2166, 1), (Sum.inr 2272, 1), (Sum.inr 3595, 1), (Sum.inr 4075, -1)]

def numericRow2163 : Integer.Sparse Master := [(Sum.inr 2148, 1), (Sum.inr 2152, 2), (Sum.inr 2166, 1), (Sum.inr 2257, 1), (Sum.inr 3592, 1), (Sum.inr 4075, -1)]

def numericRow2164 : Integer.Sparse Master := [(Sum.inr 2658, 1), (Sum.inr 3406, 1), (Sum.inr 3412, 1), (Sum.inr 3417, 2), (Sum.inr 3591, 1), (Sum.inr 4075, -1)]

def numericRow2165 : Integer.Sparse Master := [(Sum.inr 2182, 2), (Sum.inr 3455, 4), (Sum.inr 4077, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow224 : Integer.Sparse Master := [(Sum.inr 2714, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def numericRow225 : Integer.Sparse Master := [(Sum.inr 1218, 1), (Sum.inr 2486, 1), (Sum.inr 2544, 1), (Sum.inr 2619, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

def numericRow226 : Integer.Sparse Master := [(Sum.inl 0, -96), (Sum.inl 2, 50), (Sum.inl 3, -480), (Sum.inl 12, -160), (Sum.inl 26, -160), (Sum.inl 1, -390), (Sum.inr 1607, 8640), (Sum.inr 1608, 8640), (Sum.inr 1612, 8640), (Sum.inr 1619, 8640), (Sum.inr 1714, 8640), (Sum.inr 2534, 8640), (Sum.inr 2538, 8640), (Sum.inr 2588, 8640), (Sum.inr 2670, 8640), (Sum.inr 3346, 8640), (Sum.inr 3349, 8640), (Sum.inr 3355, 8640), (Sum.inr 3431, 8640), (Sum.inr 3434, 8640), (Sum.inr 3463, 8640), (Sum.inr 3503, 8640), (Sum.inr 3507, 8640), (Sum.inr 3517, 8640), (Sum.inr 3523, 8640), (Sum.inr 3539, 8640), (Sum.inr 3540, 8640), (Sum.inr 3543, 8640), (Sum.inr 3572, 8640), (Sum.inr 3606, 8640), (Sum.inr 3625, 8640), (Sum.inr 3848, 8640), (Sum.inr 3857, 8640), (Sum.inr 3884, 8640)]

def numericRow227 : Integer.Sparse Master := [(Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3902, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def numericRow228 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 1394, 1), (Sum.inr 1400, 1), (Sum.inr 1406, 1), (Sum.inr 1425, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def numericRow229 : Integer.Sparse Master := [(Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def numericRow230 : Integer.Sparse Master := [(Sum.inr 2624, 1), (Sum.inr 2949, 1), (Sum.inr 3013, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def numericRow231 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 2933, 1), (Sum.inr 3013, 1), (Sum.inr 3064, 1), (Sum.inr 3084, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def numericRow232 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2947, 1), (Sum.inr 2984, 1), (Sum.inr 2992, 1), (Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

def numericRow233 : Integer.Sparse Master := [(Sum.inr 1425, 1), (Sum.inr 2992, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 2), (Sum.inr 3108, 1), (Sum.inr 4091, -1)]

def numericRow234 : Integer.Sparse Master := [(Sum.inr 2618, 1), (Sum.inr 2933, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 3086, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def numericRow235 : Integer.Sparse Master := [(Sum.inr 1400, 1), (Sum.inr 2942, 1), (Sum.inr 2947, 1), (Sum.inr 2949, 1), (Sum.inr 2964, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

def numericRow236 : Integer.Sparse Master := [(Sum.inl 0, -812), (Sum.inl 6, 20), (Sum.inl 2, 1100), (Sum.inl 3, -640), (Sum.inl 13, 320), (Sum.inl 52, -320), (Sum.inl 1, 980), (Sum.inr 2496, 17280), (Sum.inr 2497, 17280), (Sum.inr 2498, 17280), (Sum.inr 2516, 17280), (Sum.inr 2708, 17280), (Sum.inr 2719, 17280), (Sum.inr 2722, 17280), (Sum.inr 2729, 17280), (Sum.inr 2765, 17280), (Sum.inr 2777, 17280), (Sum.inr 3028, 17280), (Sum.inr 3035, 17280), (Sum.inr 3038, 17280), (Sum.inr 3042, 17280), (Sum.inr 3063, 17280), (Sum.inr 3064, 17280), (Sum.inr 3067, 17280), (Sum.inr 3086, 34560), (Sum.inr 3092, 17280), (Sum.inr 3098, 17280), (Sum.inr 3197, 17280), (Sum.inr 3198, 17280)]

def numericRow237 : Integer.Sparse Master := [(Sum.inr 2588, 1), (Sum.inr 3502, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3540, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def numericRow238 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2054, 1), (Sum.inr 2278, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

def numericRow239 : Integer.Sparse Master := [(Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 3540, 2), (Sum.inr 3632, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow240 : Integer.Sparse Master := [(Sum.inr 2973, 1), (Sum.inr 3490, 1), (Sum.inr 3502, 1), (Sum.inr 3540, 2), (Sum.inr 4084, -1)]

def numericRow241 : Integer.Sparse Master := [(Sum.inr 2039, 1), (Sum.inr 2592, 1), (Sum.inr 3383, 1), (Sum.inr 3490, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow242 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

def numericRow243 : Integer.Sparse Master := [(Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 3540, 1), (Sum.inr 3544, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def numericRow244 : Integer.Sparse Master := [(Sum.inl 0, -772), (Sum.inl 6, 20), (Sum.inl 2, -480), (Sum.inl 3, -1600), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -320), (Sum.inl 4, -640), (Sum.inl 1, 1040), (Sum.inr 1180, 17280), (Sum.inr 1181, 17280), (Sum.inr 1182, 17280), (Sum.inr 1189, 17280), (Sum.inr 1262, 17280), (Sum.inr 2454, 17280), (Sum.inr 2465, 17280), (Sum.inr 2495, 17280), (Sum.inr 2734, 17280), (Sum.inr 2834, 17280), (Sum.inr 2835, 17280), (Sum.inr 2841, 17280), (Sum.inr 2905, 17280), (Sum.inr 2909, 17280), (Sum.inr 2976, 17280), (Sum.inr 2979, 17280), (Sum.inr 3037, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3051, 17280), (Sum.inr 3055, 17280), (Sum.inr 3573, 17280), (Sum.inr 3872, 17280)]

def numericRow245 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 2, -5), (Sum.inl 1, 10), (Sum.inr 2836, 720), (Sum.inr 2837, 720), (Sum.inr 2838, 720), (Sum.inr 2841, 720), (Sum.inr 3051, 720), (Sum.inr 3241, 720), (Sum.inr 3242, 720), (Sum.inr 3243, 720), (Sum.inr 3246, 720), (Sum.inr 3294, 720), (Sum.inr 3437, 720), (Sum.inr 3461, 720), (Sum.inr 3471, 720), (Sum.inr 3472, 720), (Sum.inr 3480, 720), (Sum.inr 3518, 720), (Sum.inr 3526, 720), (Sum.inr 3534, 720), (Sum.inr 3535, 720), (Sum.inr 3541, 720), (Sum.inr 3548, 720), (Sum.inr 3549, 720), (Sum.inr 3559, 720), (Sum.inr 3573, 720), (Sum.inr 3584, 720), (Sum.inr 3809, 720), (Sum.inr 3839, 720)]

def numericRow246 : Integer.Sparse Master := [(Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def numericRow247 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 1224, 1), (Sum.inr 1226, 1), (Sum.inr 1237, 1), (Sum.inr 1277, 1), (Sum.inr 2731, 1), (Sum.inr 4092, -1)]

def numericRow248 : Integer.Sparse Master := [(Sum.inr 1277, 1), (Sum.inr 2577, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

def numericRow249 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2495, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

def numericRow250 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 2493, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 4092, -1)]

def numericRow251 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2549, 1), (Sum.inr 2577, 1), (Sum.inr 2731, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def numericRow252 : Integer.Sparse Master := [(Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def numericRow253 : Integer.Sparse Master := [(Sum.inr 2645, 1), (Sum.inr 2647, 1), (Sum.inr 2649, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

def numericRow254 : Integer.Sparse Master := [(Sum.inr 1226, 1), (Sum.inr 2499, 1), (Sum.inr 2549, 1), (Sum.inr 2649, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

def numericRow255 : Integer.Sparse Master := [(Sum.inl 0, -192), (Sum.inl 5, -40), (Sum.inl 6, 10), (Sum.inl 2, -90), (Sum.inl 51, 480), (Sum.inl 3, -1280), (Sum.inl 13, -320), (Sum.inl 52, -160), (Sum.inl 12, -640), (Sum.inl 4, -640), (Sum.inl 1, -20), (Sum.inl 31, 480), (Sum.inr 988, 8640), (Sum.inr 989, 8640), (Sum.inr 993, 8640), (Sum.inr 1001, 8640), (Sum.inr 1057, 8640), (Sum.inr 2390, 8640), (Sum.inr 2391, 8640), (Sum.inr 2395, 8640), (Sum.inr 2401, 8640), (Sum.inr 2453, 8640), (Sum.inr 2456, 8640), (Sum.inr 2460, 8640), (Sum.inr 2493, 8640), (Sum.inr 2569, 8640), (Sum.inr 2615, 8640), (Sum.inr 2621, 8640), (Sum.inr 2664, 8640), (Sum.inr 2698, 8640), (Sum.inr 2706, 8640), (Sum.inr 2730, 8640), (Sum.inr 2731, 17280), (Sum.inr 2738, 8640), (Sum.inr 3880, 8640), (Sum.inr 3884, 8640), (Sum.inr 3885, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow256 : Integer.Sparse Master := [(Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def numericRow257 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 1361, 1), (Sum.inr 1363, 1), (Sum.inr 1370, 1), (Sum.inr 1423, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def numericRow258 : Integer.Sparse Master := [(Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 2), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

def numericRow259 : Integer.Sparse Master := [(Sum.inr 2627, 1), (Sum.inr 2946, 1), (Sum.inr 3008, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def numericRow260 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 2862, 1), (Sum.inr 3008, 1), (Sum.inr 3029, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def numericRow261 : Integer.Sparse Master := [(Sum.inr 2625, 1), (Sum.inr 2918, 1), (Sum.inr 2972, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

def numericRow262 : Integer.Sparse Master := [(Sum.inr 1423, 1), (Sum.inr 2625, 1), (Sum.inr 2627, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def numericRow263 : Integer.Sparse Master := [(Sum.inr 2862, 1), (Sum.inr 2865, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 1), (Sum.inr 3039, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def numericRow264 : Integer.Sparse Master := [(Sum.inr 1363, 1), (Sum.inr 2868, 1), (Sum.inr 2972, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 2), (Sum.inr 4091, -1)]

def numericRow265 : Integer.Sparse Master := [(Sum.inr 2641, 1), (Sum.inr 3029, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def numericRow266 : Integer.Sparse Master := [(Sum.inr 1361, 1), (Sum.inr 2865, 1), (Sum.inr 2918, 1), (Sum.inr 2946, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

def numericRow267 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 2028, -360), (Sum.inr 2058, -360), (Sum.inr 2215, -360), (Sum.inr 2216, -360), (Sum.inr 2266, -360), (Sum.inr 2278, -360), (Sum.inr 2672, -360), (Sum.inr 2722, -360), (Sum.inr 2723, -720), (Sum.inr 3054, -360), (Sum.inr 3391, -360), (Sum.inr 3533, -360), (Sum.inr 3544, -720), (Sum.inr 3626, -360), (Sum.inr 3627, -360), (Sum.inr 4803, 1440), (Sum.inr 4808, 1440), (Sum.inr 4854, 1440), (Sum.inr 4855, 1440), (Sum.inr 4870, 1440), (Sum.inr 4880, 1440), (Sum.inr 5220, 1440), (Sum.inr 5223, 1440), (Sum.inr 5229, 1440), (Sum.inr 5232, 1440), (Sum.inr 5233, 2880), (Sum.inr 5243, 1440), (Sum.inr 5244, 1440), (Sum.inr 5253, 1440), (Sum.inr 5254, 1440), (Sum.inr 5264, 1440), (Sum.inr 5266, 1440), (Sum.inr 5267, 1440), (Sum.inr 5300, 1440)]

def numericRow268 : Integer.Sparse Master := [(Sum.inl 0, -260), (Sum.inl 5, -40), (Sum.inl 2, 350), (Sum.inl 35, -160), (Sum.inl 3, -160), (Sum.inl 13, 160), (Sum.inl 55, 480), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 27, 120), (Sum.inl 1, 170), (Sum.inr 2127, 8640), (Sum.inr 2128, 8640), (Sum.inr 2129, 8640), (Sum.inr 2133, 8640), (Sum.inr 2195, 8640), (Sum.inr 2215, 8640), (Sum.inr 2216, 8640), (Sum.inr 2220, 8640), (Sum.inr 2278, 8640), (Sum.inr 2665, 8640), (Sum.inr 2677, 8640), (Sum.inr 2678, 8640), (Sum.inr 2697, 8640), (Sum.inr 2698, 8640), (Sum.inr 2713, 8640), (Sum.inr 2714, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2729, 8640), (Sum.inr 2731, 8640), (Sum.inr 2732, 8640), (Sum.inr 2774, 8640), (Sum.inr 3044, 8640), (Sum.inr 3068, 8640), (Sum.inr 3092, 8640)]

def numericRow269 : Integer.Sparse Master := [(Sum.inl 0, -804), (Sum.inl 5, 160), (Sum.inl 6, 20), (Sum.inl 2, 1040), (Sum.inl 7, -320), (Sum.inl 35, -640), (Sum.inl 3, -960), (Sum.inl 13, -640), (Sum.inl 52, -320), (Sum.inl 54, 960), (Sum.inl 12, -320), (Sum.inl 26, -320), (Sum.inl 1, 1280), (Sum.inr 2091, 17280), (Sum.inr 2092, 17280), (Sum.inr 2093, 17280), (Sum.inr 2111, 17280), (Sum.inr 2254, 17280), (Sum.inr 2662, 17280), (Sum.inr 2672, 17280), (Sum.inr 2673, 17280), (Sum.inr 2678, 17280), (Sum.inr 2723, 17280), (Sum.inr 3016, 17280), (Sum.inr 3017, 17280), (Sum.inr 3019, 17280), (Sum.inr 3029, 17280), (Sum.inr 3030, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3040, 17280), (Sum.inr 3044, 17280), (Sum.inr 3045, 17280), (Sum.inr 3054, 17280), (Sum.inr 3055, 17280), (Sum.inr 3202, 17280)]

def numericRow270 : Integer.Sparse Master := [(Sum.inr 3388, 1), (Sum.inr 3391, 1), (Sum.inr 3392, 1), (Sum.inr 3395, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

def numericRow271 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2266, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow272 : Integer.Sparse Master := [(Sum.inr 2266, 1), (Sum.inr 3535, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow273 : Integer.Sparse Master := [(Sum.inr 3159, 1), (Sum.inr 3377, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 2), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def numericRow274 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 3377, 1), (Sum.inr 3504, 1), (Sum.inr 3528, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def numericRow275 : Integer.Sparse Master := [(Sum.inr 3153, 1), (Sum.inr 3388, 1), (Sum.inr 3488, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 2), (Sum.inr 4084, -1)]

def numericRow276 : Integer.Sparse Master := [(Sum.inr 2026, 1), (Sum.inr 3153, 1), (Sum.inr 3156, 1), (Sum.inr 3157, 1), (Sum.inr 3159, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def numericRow277 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 2), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow278 : Integer.Sparse Master := [(Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

def numericRow279 : Integer.Sparse Master := [(Sum.inr 3157, 1), (Sum.inr 3392, 1), (Sum.inr 3504, 1), (Sum.inr 3506, 1), (Sum.inr 3535, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow280 : Integer.Sparse Master := [(Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 3488, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

def numericRow281 : Integer.Sparse Master := [(Sum.inl 0, -464), (Sum.inl 5, -80), (Sum.inl 6, 20), (Sum.inl 2, -440), (Sum.inl 35, -320), (Sum.inl 3, -1920), (Sum.inl 13, -640), (Sum.inl 52, -320), (Sum.inl 12, -640), (Sum.inl 26, -640), (Sum.inl 4, -640), (Sum.inl 1, 660), (Sum.inr 1178, 17280), (Sum.inr 1179, 17280), (Sum.inr 1182, 17280), (Sum.inr 1185, 17280), (Sum.inr 1261, 17280), (Sum.inr 1992, 17280), (Sum.inr 2004, 17280), (Sum.inr 2035, 17280), (Sum.inr 2197, 17280), (Sum.inr 2833, 17280), (Sum.inr 2835, 17280), (Sum.inr 2838, 17280), (Sum.inr 2905, 17280), (Sum.inr 2907, 17280), (Sum.inr 2933, 17280), (Sum.inr 2974, 17280), (Sum.inr 2979, 17280), (Sum.inr 3016, 17280), (Sum.inr 3025, 17280), (Sum.inr 3037, 17280), (Sum.inr 3039, 17280), (Sum.inr 3051, 17280), (Sum.inr 3086, 17280), (Sum.inr 3541, 17280), (Sum.inr 3814, 17280), (Sum.inr 3841, 17280)]

def numericRow282 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, -20), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 55), (Sum.inr 2001, 2160), (Sum.inr 2004, 2160), (Sum.inr 2005, 2160), (Sum.inr 2055, 2160), (Sum.inr 2207, 2160), (Sum.inr 2833, 2160), (Sum.inr 2835, 2160), (Sum.inr 2838, 2160), (Sum.inr 3038, 2160), (Sum.inr 3238, 2160), (Sum.inr 3240, 2160), (Sum.inr 3243, 2160), (Sum.inr 3296, 2160), (Sum.inr 3464, 2160), (Sum.inr 3479, 2160), (Sum.inr 3480, 2160), (Sum.inr 3517, 2160), (Sum.inr 3518, 2160), (Sum.inr 3526, 2160), (Sum.inr 3528, 2160), (Sum.inr 3534, 2160), (Sum.inr 3535, 2160), (Sum.inr 3540, 2160), (Sum.inr 3561, 2160), (Sum.inr 3573, 2160), (Sum.inr 3577, 2160), (Sum.inr 3814, 2160), (Sum.inr 3841, 2160)]

def numericRow283 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 3814, 2), (Sum.inr 3841, 1), (Sum.inr 3906, 1), (Sum.inr 4092, -1)]

def numericRow284 : Integer.Sparse Master := [(Sum.inr 1278, 1), (Sum.inr 2578, 1), (Sum.inr 2649, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

def numericRow285 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2497, 1), (Sum.inr 2499, 1), (Sum.inr 2515, 1), (Sum.inr 2732, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

def numericRow286 : Integer.Sparse Master := [(Sum.inl 0, -111), (Sum.inl 5, -20), (Sum.inl 6, 5), (Sum.inl 2, -80), (Sum.inl 51, 240), (Sum.inl 13, 80), (Sum.inl 52, -80), (Sum.inl 12, 160), (Sum.inl 1, -50), (Sum.inr 990, 4320), (Sum.inr 991, 4320), (Sum.inr 992, 4320), (Sum.inr 1006, 4320), (Sum.inr 1058, 4320), (Sum.inr 2392, 4320), (Sum.inr 2393, 4320), (Sum.inr 2394, 4320), (Sum.inr 2405, 4320), (Sum.inr 2454, 4320), (Sum.inr 2455, 4320), (Sum.inr 2463, 4320), (Sum.inr 2494, 4320), (Sum.inr 2617, 4320), (Sum.inr 2618, 4320), (Sum.inr 2620, 4320), (Sum.inr 2728, 4320), (Sum.inr 2729, 4320), (Sum.inr 2732, 4320), (Sum.inr 2734, 4320), (Sum.inr 2735, 4320), (Sum.inr 2744, 4320), (Sum.inr 2773, 4320), (Sum.inr 3872, 4320), (Sum.inr 3876, 4320), (Sum.inr 3877, 4320)]

def numericRow287 : Integer.Sparse Master := [(Sum.inl 0, -100), (Sum.inl 2, -30), (Sum.inl 3, -160), (Sum.inl 12, 160), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, -50), (Sum.inr 1609, 8640), (Sum.inr 1610, 8640), (Sum.inr 1611, 8640), (Sum.inr 1624, 8640), (Sum.inr 1715, 8640), (Sum.inr 2906, 8640), (Sum.inr 2910, 8640), (Sum.inr 2952, 8640), (Sum.inr 3052, 8640), (Sum.inr 3347, 8640), (Sum.inr 3348, 8640), (Sum.inr 3358, 8640), (Sum.inr 3430, 8640), (Sum.inr 3437, 8640), (Sum.inr 3464, 8640), (Sum.inr 3505, 8640), (Sum.inr 3506, 8640), (Sum.inr 3523, 8640), (Sum.inr 3537, 8640), (Sum.inr 3538, 8640), (Sum.inr 3541, 8640), (Sum.inr 3549, 8640), (Sum.inr 3573, 8640), (Sum.inr 3624, 8640), (Sum.inr 3626, 8640), (Sum.inr 3839, 8640), (Sum.inr 3845, 8640), (Sum.inr 3877, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow288 : Integer.Sparse Master := [(Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def numericRow289 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 1359, 1), (Sum.inr 1362, 1), (Sum.inr 1367, 1), (Sum.inr 1422, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def numericRow290 : Integer.Sparse Master := [(Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3051, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

def numericRow291 : Integer.Sparse Master := [(Sum.inr 2579, 1), (Sum.inr 2582, 1), (Sum.inr 3007, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

def numericRow292 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 2861, 1), (Sum.inr 3007, 1), (Sum.inr 3036, 1), (Sum.inr 3038, 2), (Sum.inr 4092, -1)]

def numericRow293 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2580, 1), (Sum.inr 2971, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

def numericRow294 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2861, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 3038, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

def numericRow295 : Integer.Sparse Master := [(Sum.inr 1362, 1), (Sum.inr 2867, 1), (Sum.inr 2971, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3040, 1), (Sum.inr 4092, -1)]

def numericRow296 : Integer.Sparse Master := [(Sum.inl 0, -484), (Sum.inl 5, -80), (Sum.inl 6, 20), (Sum.inl 2, 640), (Sum.inl 35, -320), (Sum.inl 3, -320), (Sum.inl 13, 320), (Sum.inl 52, -320), (Sum.inl 12, 320), (Sum.inl 1, 320), (Sum.inr 2036, 17280), (Sum.inr 2037, 17280), (Sum.inr 2038, 17280), (Sum.inr 2059, 17280), (Sum.inr 2254, 17280), (Sum.inr 2661, 17280), (Sum.inr 2670, 17280), (Sum.inr 2672, 17280), (Sum.inr 2677, 17280), (Sum.inr 2722, 17280), (Sum.inr 3015, 17280), (Sum.inr 3016, 17280), (Sum.inr 3018, 17280), (Sum.inr 3028, 17280), (Sum.inr 3029, 17280), (Sum.inr 3035, 17280), (Sum.inr 3038, 17280), (Sum.inr 3039, 17280), (Sum.inr 3042, 17280), (Sum.inr 3044, 17280), (Sum.inr 3052, 17280), (Sum.inr 3054, 17280), (Sum.inr 3064, 17280), (Sum.inr 3086, 17280), (Sum.inr 3196, 17280), (Sum.inr 3198, 17280)]

def numericRow297 : Integer.Sparse Master := [(Sum.inr 2560, 1), (Sum.inr 3375, 1), (Sum.inr 3379, 1), (Sum.inr 3391, 1), (Sum.inr 3533, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow298 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2037, 1), (Sum.inr 2039, 1), (Sum.inr 2058, 1), (Sum.inr 2279, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow299 : Integer.Sparse Master := [(Sum.inr 3151, 1), (Sum.inr 3379, 1), (Sum.inr 3382, 1), (Sum.inr 3383, 1), (Sum.inr 3395, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow300 : Integer.Sparse Master := [(Sum.inr 2034, 1), (Sum.inr 2555, 1), (Sum.inr 3382, 1), (Sum.inr 3528, 1), (Sum.inr 3539, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

def numericRow301 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -140), (Sum.inr 3279, 2160), (Sum.inr 3280, 2160), (Sum.inr 3282, 2160), (Sum.inr 3290, 4320), (Sum.inr 3434, 4320), (Sum.inr 3466, 2160), (Sum.inr 3467, 4320), (Sum.inr 3476, 2160), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3536, 4320), (Sum.inr 3539, 2160), (Sum.inr 3543, 2160), (Sum.inr 3544, 4320), (Sum.inr 3568, 4320), (Sum.inr 3571, 2160), (Sum.inr 3580, 2160), (Sum.inr 3805, 2160), (Sum.inr 3848, 4320)]

def numericRow302 : Integer.Sparse Master := [(Sum.inr 3800, 1), (Sum.inr 3871, 2), (Sum.inr 3901, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

def numericRow303 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1208, 1), (Sum.inr 1213, 2), (Sum.inr 1247, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow304 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 2622, 2), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

def numericRow305 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 2), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

def numericRow306 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 2480, 1), (Sum.inr 2615, 1), (Sum.inr 2721, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def numericRow307 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2612, 1), (Sum.inr 2615, 1), (Sum.inr 2622, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

def numericRow308 : Integer.Sparse Master := [(Sum.inr 1208, 1), (Sum.inr 2473, 1), (Sum.inr 2612, 2), (Sum.inr 2710, 1), (Sum.inr 4091, -1)]

def numericRow309 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 2019, -180), (Sum.inr 2051, -180), (Sum.inr 2190, -180), (Sum.inr 2191, -180), (Sum.inr 2244, -180), (Sum.inr 2262, -180), (Sum.inr 2694, -180), (Sum.inr 2722, -360), (Sum.inr 2723, -720), (Sum.inr 3077, -180), (Sum.inr 3493, -180), (Sum.inr 3533, -360), (Sum.inr 3544, -720), (Sum.inr 3625, -180), (Sum.inr 3627, -360), (Sum.inr 4803, 1440), (Sum.inr 5219, 720), (Sum.inr 5220, 720), (Sum.inr 5223, 1440), (Sum.inr 5244, 720), (Sum.inr 5249, 720), (Sum.inr 5251, 720), (Sum.inr 5253, 1440), (Sum.inr 5254, 1440), (Sum.inr 5266, 1440), (Sum.inr 5282, 720)]

def numericRow310 : Integer.Sparse Master := [(Sum.inl 0, -222), (Sum.inl 5, 20), (Sum.inl 2, 255), (Sum.inl 35, 80), (Sum.inl 55, -240), (Sum.inl 26, 160), (Sum.inl 27, -60), (Sum.inl 1, 265), (Sum.inr 2190, 4320), (Sum.inr 2191, 4320), (Sum.inr 2195, 8640), (Sum.inr 2244, 4320), (Sum.inr 2661, 4320), (Sum.inr 2662, 4320), (Sum.inr 2665, 8640), (Sum.inr 2708, 4320), (Sum.inr 2710, 4320), (Sum.inr 2713, 8640), (Sum.inr 2714, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 8640), (Sum.inr 2731, 8640), (Sum.inr 2751, 4320), (Sum.inr 3029, 4320)]

def numericRow311 : Integer.Sparse Master := [(Sum.inl 0, -688), (Sum.inl 5, -120), (Sum.inl 6, 20), (Sum.inl 2, 920), (Sum.inl 7, 160), (Sum.inl 35, 480), (Sum.inl 3, 160), (Sum.inl 13, 640), (Sum.inl 52, 320), (Sum.inl 54, -480), (Sum.inl 12, 160), (Sum.inl 1, 780), (Sum.inr 2694, 8640), (Sum.inr 2698, 8640), (Sum.inr 2723, 17280), (Sum.inr 3016, 17280), (Sum.inr 3017, 17280), (Sum.inr 3019, 17280), (Sum.inr 3039, 17280), (Sum.inr 3064, 8640), (Sum.inr 3066, 8640), (Sum.inr 3068, 8640), (Sum.inr 3069, 8640), (Sum.inr 3077, 8640), (Sum.inr 3078, 8640), (Sum.inr 3202, 17280)]

def numericRow312 : Integer.Sparse Master := [(Sum.inr 3493, 1), (Sum.inr 3497, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

def numericRow313 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2021, 2), (Sum.inr 2051, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

def numericRow314 : Integer.Sparse Master := [(Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 3625, 1), (Sum.inr 3627, 2), (Sum.inr 4084, -1)]

def numericRow315 : Integer.Sparse Master := [(Sum.inr 3375, 1), (Sum.inr 3377, 2), (Sum.inr 3388, 1), (Sum.inr 3497, 1), (Sum.inr 4084, -1)]

def numericRow316 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 3388, 1), (Sum.inr 3539, 1), (Sum.inr 3544, 2), (Sum.inr 4084, -1)]

def numericRow317 : Integer.Sparse Master := [(Sum.inr 3502, 1), (Sum.inr 3504, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def numericRow318 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 3375, 1), (Sum.inr 3502, 1), (Sum.inr 3533, 2), (Sum.inr 4084, -1)]

def numericRow319 : Integer.Sparse Master := [(Sum.inl 0, -31), (Sum.inl 2, 75), (Sum.inl 3, 720), (Sum.inl 13, 320), (Sum.inl 12, 160), (Sum.inl 4, 160), (Sum.inl 1, -210), (Sum.inr 1995, 4320), (Sum.inr 1998, 8640), (Sum.inr 2050, 4320), (Sum.inr 2201, 4320), (Sum.inr 3278, 4320), (Sum.inr 3280, 4320), (Sum.inr 3288, 8640), (Sum.inr 3476, 4320), (Sum.inr 3477, 8640), (Sum.inr 3532, 8640), (Sum.inr 3536, 8640), (Sum.inr 3537, 8640), (Sum.inr 3539, 8640), (Sum.inr 3571, 4320), (Sum.inr 3574, 8640), (Sum.inr 3576, 4320), (Sum.inr 3812, 4320), (Sum.inr 3840, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow32 : Integer.Sparse Master := [(Sum.inr 1067, 2), (Sum.inr 2041, 2), (Sum.inr 2284, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def numericRow33 : Integer.Sparse Master := [(Sum.inr 1459, 1), (Sum.inr 2041, 2), (Sum.inr 2063, 2), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def numericRow34 : Integer.Sparse Master := [(Sum.inr 1069, 2), (Sum.inr 1459, 3), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

def numericRow35 : Integer.Sparse Master := [(Sum.inl 0, -27), (Sum.inl 2, 70), (Sum.inl 3, 80), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 25), (Sum.inr 795, 4320), (Sum.inr 797, 2160), (Sum.inr 814, 2160), (Sum.inr 829, 2160), (Sum.inr 1355, 4320), (Sum.inr 1369, 2160), (Sum.inr 1408, 2160), (Sum.inr 1903, 4320), (Sum.inr 1916, 4320), (Sum.inr 1927, 4320), (Sum.inr 2037, 4320), (Sum.inr 2063, 2160), (Sum.inr 2092, 4320), (Sum.inr 2113, 2160), (Sum.inr 2254, 4320), (Sum.inr 2267, 2160), (Sum.inr 2280, 2160), (Sum.inr 3054, 2160), (Sum.inr 3222, 4320)]

def numericRow36 : Integer.Sparse Master := [(Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

def numericRow37 : Integer.Sparse Master := [(Sum.inr 1029, 2), (Sum.inr 1031, 1), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def numericRow38 : Integer.Sparse Master := [(Sum.inr 1029, 1), (Sum.inr 2013, 1), (Sum.inr 2096, 1), (Sum.inr 2125, 1), (Sum.inr 2253, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def numericRow39 : Integer.Sparse Master := [(Sum.inr 1458, 1), (Sum.inr 2013, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2255, 1), (Sum.inr 3156, 1), (Sum.inr 4084, -1)]

def numericRow40 : Integer.Sparse Master := [(Sum.inr 1061, 1), (Sum.inr 2037, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

def numericRow41 : Integer.Sparse Master := [(Sum.inr 1462, 1), (Sum.inr 2096, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3161, 1), (Sum.inr 4084, -1)]

def numericRow42 : Integer.Sparse Master := [(Sum.inr 1047, 1), (Sum.inr 2026, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def numericRow43 : Integer.Sparse Master := [(Sum.inr 1461, 1), (Sum.inr 2125, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 4084, -1)]

def numericRow44 : Integer.Sparse Master := [(Sum.inr 1031, 1), (Sum.inr 1458, 2), (Sum.inr 1461, 1), (Sum.inr 1462, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

def numericRow45 : Integer.Sparse Master := [(Sum.inr 1084, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 2290, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

def numericRow46 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 1067, 1), (Sum.inr 1068, 1), (Sum.inr 1084, 1), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

def numericRow47 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 2040, 1), (Sum.inr 2283, 1), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow320 : Integer.Sparse Master := [(Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 2), (Sum.inr 3899, 1), (Sum.inr 3901, 1), (Sum.inr 4091, -1)]

def numericRow321 : Integer.Sparse Master := [(Sum.inr 1248, 1), (Sum.inr 2623, 2), (Sum.inr 2710, 1), (Sum.inr 2745, 1), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

def numericRow322 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2473, 1), (Sum.inr 2483, 2), (Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

def numericRow323 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 2617, 1), (Sum.inr 2710, 2), (Sum.inr 2721, 1), (Sum.inr 4091, -1)]

def numericRow324 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2612, 1), (Sum.inr 2617, 1), (Sum.inr 2623, 1), (Sum.inr 2710, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

def numericRow325 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 2710, 3), (Sum.inr 2745, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

def numericRow326 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 190), (Sum.inr 2924, -8640), (Sum.inr 3077, -4320), (Sum.inr 3605, -8640), (Sum.inr 3625, -4320), (Sum.inr 3838, -8640), (Sum.inr 3843, -8640), (Sum.inr 3902, -4320), (Sum.inr 4391, 17280), (Sum.inr 4392, 17280), (Sum.inr 4400, 34560), (Sum.inr 4439, 17280), (Sum.inr 4992, 17280), (Sum.inr 4993, 17280), (Sum.inr 4999, 34560), (Sum.inr 5128, 34560), (Sum.inr 5129, 34560), (Sum.inr 5138, 34560), (Sum.inr 5249, 17280), (Sum.inr 5252, 17280), (Sum.inr 5255, 34560), (Sum.inr 5260, 34560), (Sum.inr 5281, 17280), (Sum.inr 5429, 17280)]

def numericRow327 : Integer.Sparse Master := [(Sum.inl 0, -125), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, 210), (Sum.inl 7, 320), (Sum.inl 35, 160), (Sum.inl 8, 160), (Sum.inl 51, -480), (Sum.inl 3, 1200), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 12, 480), (Sum.inl 26, 160), (Sum.inl 4, 320), (Sum.inl 1, -445), (Sum.inr 972, 4320), (Sum.inr 973, 4320), (Sum.inr 981, 8640), (Sum.inr 1021, 4320), (Sum.inr 2378, 4320), (Sum.inr 2379, 4320), (Sum.inr 2384, 8640), (Sum.inr 2543, 8640), (Sum.inr 2545, 8640), (Sum.inr 2557, 8640), (Sum.inr 2708, 4320), (Sum.inr 2712, 4320), (Sum.inr 2718, 8640), (Sum.inr 2724, 8640), (Sum.inr 2750, 4320), (Sum.inr 3954, 4320)]

def numericRow328 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 1606, 4320), (Sum.inr 1607, 8640), (Sum.inr 1613, 4320), (Sum.inr 1713, 4320), (Sum.inr 3345, 4320), (Sum.inr 3346, 8640), (Sum.inr 3350, 4320), (Sum.inr 3502, 4320), (Sum.inr 3503, 8640), (Sum.inr 3516, 8640), (Sum.inr 3517, 8640), (Sum.inr 3519, 8640), (Sum.inr 3540, 8640), (Sum.inr 3543, 4320), (Sum.inr 3571, 4320), (Sum.inr 3605, 8640), (Sum.inr 3625, 4320), (Sum.inr 3843, 8640), (Sum.inr 3874, 4320)]

def numericRow329 : Integer.Sparse Master := [(Sum.inr 3064, 1), (Sum.inr 3838, 2), (Sum.inr 3846, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

def numericRow330 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 1380, 1), (Sum.inr 1383, 1), (Sum.inr 1392, 2), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

def numericRow331 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 2924, 2), (Sum.inr 3064, 1), (Sum.inr 3074, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def numericRow332 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 3012, 1), (Sum.inr 3013, 2), (Sum.inr 3064, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

def numericRow333 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 3064, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

def numericRow334 : Integer.Sparse Master := [(Sum.inr 1380, 1), (Sum.inr 2916, 2), (Sum.inr 3012, 1), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 4091, -1)]

def numericRow335 : Integer.Sparse Master := [(Sum.inl 0, -207), (Sum.inl 5, 20), (Sum.inl 6, -10), (Sum.inl 2, 265), (Sum.inl 35, 80), (Sum.inl 3, 320), (Sum.inl 13, 80), (Sum.inl 52, 160), (Sum.inl 1, 330), (Sum.inr 2694, 4320), (Sum.inr 2697, 4320), (Sum.inr 2722, 8640), (Sum.inr 3015, 8640), (Sum.inr 3016, 8640), (Sum.inr 3018, 8640), (Sum.inr 3038, 8640), (Sum.inr 3063, 4320), (Sum.inr 3067, 4320), (Sum.inr 3068, 4320), (Sum.inr 3075, 4320), (Sum.inr 3077, 4320), (Sum.inr 3086, 8640), (Sum.inr 3196, 8640), (Sum.inr 3197, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow336 : Integer.Sparse Master := [(Sum.inr 3488, 1), (Sum.inr 3493, 1), (Sum.inr 3533, 2), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

def numericRow337 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2034, 2), (Sum.inr 2051, 1), (Sum.inr 2277, 1), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

def numericRow338 : Integer.Sparse Master := [(Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 3539, 1), (Sum.inr 3625, 1), (Sum.inr 3632, 2), (Sum.inr 4084, -1)]

def numericRow339 : Integer.Sparse Master := [(Sum.inl 0, 61), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, 80), (Sum.inl 1, 390), (Sum.inr 1294, -2160), (Sum.inr 1297, -720), (Sum.inr 2112, -2160), (Sum.inr 2281, -720), (Sum.inr 2287, -2160), (Sum.inr 2289, -720), (Sum.inr 2294, -720), (Sum.inr 2954, -4320), (Sum.inr 3054, -2160), (Sum.inr 3305, -2160), (Sum.inr 3311, -720), (Sum.inr 3606, -4320), (Sum.inr 3614, -2160), (Sum.inr 3623, -2160), (Sum.inr 3626, -2160), (Sum.inr 3907, -2160)]

def numericRow340 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1294, 720), (Sum.inr 1297, 240), (Sum.inr 2112, 720), (Sum.inr 2281, 240), (Sum.inr 2954, 1440), (Sum.inr 3054, 720)]

def numericRow341 : Integer.Sparse Master := [(Sum.inl 0, 57), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 4, 80), (Sum.inl 1, -95), (Sum.inr 1087, -2160), (Sum.inr 1091, -720), (Sum.inr 1094, -720), (Sum.inr 1739, -2160), (Sum.inr 1741, -720), (Sum.inr 1756, -720), (Sum.inr 2515, -4320), (Sum.inr 2519, -2160), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2782, -2160), (Sum.inr 2783, -1440), (Sum.inr 3479, -4320), (Sum.inr 3486, -2160), (Sum.inr 3583, -2160), (Sum.inr 3632, -2160), (Sum.inr 3634, -720), (Sum.inr 3913, -2160)]

def numericRow342 : Integer.Sparse Master := [(Sum.inl 0, -5), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 8), (Sum.inr 1087, 216), (Sum.inr 1091, 72), (Sum.inr 1094, 72), (Sum.inr 2515, 432), (Sum.inr 2519, 216), (Sum.inr 2522, 216), (Sum.inr 2782, 216), (Sum.inr 2783, 72)]

def numericRow343 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2281, -720), (Sum.inr 2294, -720), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 2783, -1440), (Sum.inr 3548, -2160), (Sum.inr 3582, -2160), (Sum.inr 3632, -2160), (Sum.inr 5260, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640), (Sum.inr 5311, 2880)]

def numericRow344 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2266, 1080), (Sum.inr 2294, 360), (Sum.inr 2724, 2160), (Sum.inr 2743, 1080), (Sum.inr 2744, 1080), (Sum.inr 2769, 1080), (Sum.inr 2789, 360)]

def numericRow345 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2765, 720), (Sum.inr 2777, 720), (Sum.inr 2783, 240), (Sum.inr 2789, 240), (Sum.inr 3086, 1440), (Sum.inr 3098, 720)]

def numericRow346 : Integer.Sparse Master := [(Sum.inr 2783, 1), (Sum.inr 3582, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def numericRow347 : Integer.Sparse Master := [(Sum.inr 3632, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def numericRow348 : Integer.Sparse Master := [(Sum.inr 3548, 3), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

def numericRow349 : Integer.Sparse Master := [(Sum.inl 0, -9), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, -25), (Sum.inr 1088, 2160), (Sum.inr 1092, 720), (Sum.inr 1093, 720), (Sum.inr 2516, 4320), (Sum.inr 2520, 2160), (Sum.inr 2521, 2160), (Sum.inr 2761, 2160), (Sum.inr 2777, 2160), (Sum.inr 2780, 720), (Sum.inr 2783, 720), (Sum.inr 3098, 2160)]

def numericRow350 : Integer.Sparse Master := [(Sum.inr 1303, 3), (Sum.inr 1309, 1), (Sum.inr 1310, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def numericRow351 : Integer.Sparse Master := [(Sum.inr 1303, 1), (Sum.inr 2134, 1), (Sum.inr 2597, 2), (Sum.inr 2781, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow352 : Integer.Sparse Master := [(Sum.inr 1310, 1), (Sum.inr 2603, 3), (Sum.inr 2783, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

def numericRow353 : Integer.Sparse Master := [(Sum.inl 0, 11), (Sum.inl 2, 5), (Sum.inl 1, -10), (Sum.inr 1240, -180), (Sum.inr 1242, -90), (Sum.inr 1246, -90), (Sum.inr 2485, -180), (Sum.inr 2519, -90), (Sum.inr 2884, -180), (Sum.inr 2889, -90), (Sum.inr 2931, -180), (Sum.inr 3299, -180), (Sum.inr 3300, -90), (Sum.inr 3301, -90), (Sum.inr 3309, -90), (Sum.inr 3481, -180), (Sum.inr 3486, -90), (Sum.inr 3607, -180), (Sum.inr 3612, -180), (Sum.inr 3621, -180), (Sum.inr 3622, -180), (Sum.inr 3627, -180), (Sum.inr 3631, -90), (Sum.inr 3632, -90), (Sum.inr 3634, -90), (Sum.inr 3903, -180), (Sum.inr 3913, -90)]

def numericRow354 : Integer.Sparse Master := [(Sum.inl 0, -11), (Sum.inl 2, -5), (Sum.inl 1, 10), (Sum.inr 1240, 180), (Sum.inr 1242, 90), (Sum.inr 1246, 90), (Sum.inr 2485, 180), (Sum.inr 2519, 90), (Sum.inr 2884, 180), (Sum.inr 2889, 90), (Sum.inr 2931, 180)]

def numericRow355 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, 15), (Sum.inl 1, 50), (Sum.inr 1041, -720), (Sum.inr 1043, -360), (Sum.inr 1050, -360), (Sum.inr 1083, -360), (Sum.inr 1724, -720), (Sum.inr 1725, -360), (Sum.inr 1728, -360), (Sum.inr 1751, -360), (Sum.inr 2480, -720), (Sum.inr 2482, -720), (Sum.inr 2489, -720), (Sum.inr 2512, -720), (Sum.inr 2723, -720), (Sum.inr 2726, -360), (Sum.inr 2743, -360), (Sum.inr 3467, -720), (Sum.inr 3468, -720), (Sum.inr 3471, -720), (Sum.inr 3482, -720), (Sum.inr 3544, -720), (Sum.inr 3545, -360), (Sum.inr 3548, -360), (Sum.inr 3607, -720), (Sum.inr 3608, -360), (Sum.inr 3616, -360), (Sum.inr 3622, -720), (Sum.inr 3623, -360), (Sum.inr 3627, -360), (Sum.inr 4047, -720)]

def numericRow356 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 2, -1), (Sum.inl 1, -2), (Sum.inr 1041, 48), (Sum.inr 1043, 24), (Sum.inr 1050, 24), (Sum.inr 1083, 24), (Sum.inr 2480, 48), (Sum.inr 2482, 48), (Sum.inr 2489, 48), (Sum.inr 2512, 48), (Sum.inr 2723, 48), (Sum.inr 2726, 24), (Sum.inr 2743, 24)]

def numericRow357 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -85), (Sum.inl 3, -80), (Sum.inl 1, -100), (Sum.inr 2244, -4320), (Sum.inr 2262, -4320), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -8640), (Sum.inr 2743, -2160), (Sum.inr 2765, -2160), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -8640), (Sum.inr 3548, -2160), (Sum.inr 3582, -2160), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -4320), (Sum.inr 3632, -2160), (Sum.inr 5266, 17280), (Sum.inr 5282, 17280), (Sum.inr 5300, 8640)]

def numericRow358 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 2244, 120), (Sum.inr 2278, 60), (Sum.inr 2722, 120), (Sum.inr 2723, 120), (Sum.inr 2731, 120), (Sum.inr 2751, 120), (Sum.inr 2765, 60), (Sum.inr 2774, 60)]

def numericRow359 : Integer.Sparse Master := [(Sum.inl 0, -4), (Sum.inl 2, 5), (Sum.inl 1, 5), (Sum.inr 2723, 90), (Sum.inr 2743, 45), (Sum.inr 3039, 90), (Sum.inr 3054, 45), (Sum.inr 3055, 45), (Sum.inr 3077, 90), (Sum.inr 3078, 90)]

def numericRow360 : Integer.Sparse Master := [(Sum.inr 3544, 2), (Sum.inr 3548, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow361 : Integer.Sparse Master := [(Sum.inr 2262, 2), (Sum.inr 2266, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow362 : Integer.Sparse Master := [(Sum.inr 3627, 3), (Sum.inr 4084, -1)]

def numericRow363 : Integer.Sparse Master := [(Sum.inr 3548, 1), (Sum.inr 3580, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow364 : Integer.Sparse Master := [(Sum.inr 3533, 2), (Sum.inr 3582, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

def numericRow365 : Integer.Sparse Master := [(Sum.inl 0, 233), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 12, -80), (Sum.inl 1, -90), (Sum.inr 1236, -4320), (Sum.inr 1239, -2160), (Sum.inr 1246, -2160), (Sum.inr 2025, -4320), (Sum.inr 2062, -2160), (Sum.inr 2224, -4320), (Sum.inr 2226, -2160), (Sum.inr 2230, -2160), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 3077, -4320), (Sum.inr 3293, -4320), (Sum.inr 3301, -2160), (Sum.inr 3308, -2160), (Sum.inr 3605, -4320), (Sum.inr 3612, -4320), (Sum.inr 3613, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3627, -2160), (Sum.inr 3631, -2160), (Sum.inr 3632, -2160), (Sum.inr 3906, -4320), (Sum.inr 3907, -2160)]

def numericRow366 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 1236, 1440), (Sum.inr 1239, 720), (Sum.inr 1246, 720), (Sum.inr 2025, 1440), (Sum.inr 2062, 720), (Sum.inr 2247, 720), (Sum.inr 2881, 1440), (Sum.inr 2889, 720), (Sum.inr 2924, 1440), (Sum.inr 2931, 1440), (Sum.inr 3077, 1440)]

def numericRow367 : Integer.Sparse Master := [(Sum.inl 0, 236), (Sum.inl 2, 75), (Sum.inl 3, 240), (Sum.inl 4, -80), (Sum.inl 1, -165), (Sum.inr 1044, -4320), (Sum.inr 1046, -2160), (Sum.inr 1049, -2160), (Sum.inr 1087, -2160), (Sum.inr 1737, -4320), (Sum.inr 1738, -2160), (Sum.inr 1739, -2160), (Sum.inr 1750, -2160), (Sum.inr 2483, -4320), (Sum.inr 2485, -4320), (Sum.inr 2488, -4320), (Sum.inr 2515, -4320), (Sum.inr 2764, -4320), (Sum.inr 2765, -2160), (Sum.inr 2782, -2160), (Sum.inr 3477, -4320), (Sum.inr 3478, -4320), (Sum.inr 3479, -4320), (Sum.inr 3481, -4320), (Sum.inr 3581, -4320), (Sum.inr 3582, -2160), (Sum.inr 3583, -2160), (Sum.inr 3613, -4320), (Sum.inr 3614, -2160), (Sum.inr 3615, -2160), (Sum.inr 3632, -4320), (Sum.inr 3633, -2160), (Sum.inr 3634, -2160), (Sum.inr 3903, -4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow368 : Integer.Sparse Master := [(Sum.inl 0, -71), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 1044, 1440), (Sum.inr 1046, 720), (Sum.inr 1049, 720), (Sum.inr 1087, 720), (Sum.inr 2483, 1440), (Sum.inr 2485, 1440), (Sum.inr 2488, 1440), (Sum.inr 2515, 1440), (Sum.inr 2764, 1440), (Sum.inr 2765, 720), (Sum.inr 2782, 720)]

def numericRow369 : Integer.Sparse Master := [(Sum.inl 0, 77), (Sum.inl 2, -95), (Sum.inl 3, 80), (Sum.inl 1, -80), (Sum.inr 2245, -4320), (Sum.inr 2266, -2160), (Sum.inr 2277, -4320), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -4320), (Sum.inr 3633, -2160), (Sum.inr 5251, 17280), (Sum.inr 5260, 17280), (Sum.inr 5267, 17280), (Sum.inr 5270, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640)]

def numericRow370 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 2, 65), (Sum.inl 3, -80), (Sum.inl 1, 50), (Sum.inr 2245, 1440), (Sum.inr 2266, 720), (Sum.inr 2279, 720), (Sum.inr 2710, 1440), (Sum.inr 2723, 1440), (Sum.inr 2724, 1440), (Sum.inr 2732, 1440), (Sum.inr 2754, 1440), (Sum.inr 2769, 720), (Sum.inr 2777, 720)]

def numericRow371 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 2, -5), (Sum.inl 3, 240), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 60), (Sum.inr 1229, 4320), (Sum.inr 1231, 2160), (Sum.inr 1245, 2160), (Sum.inr 1292, 2160), (Sum.inr 1639, 4320), (Sum.inr 1651, 2160), (Sum.inr 1716, 2160), (Sum.inr 2875, 4320), (Sum.inr 2888, 2160), (Sum.inr 2921, 4320), (Sum.inr 2930, 4320), (Sum.inr 2952, 4320), (Sum.inr 3024, 4320), (Sum.inr 3052, 2160), (Sum.inr 3097, 4320), (Sum.inr 3573, 4320), (Sum.inr 3584, 2160), (Sum.inr 3626, 2160)]

def numericRow372 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 5), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -10), (Sum.inr 1070, 4320), (Sum.inr 1072, 2160), (Sum.inr 1076, 2160), (Sum.inr 1084, 2160), (Sum.inr 2500, 4320), (Sum.inr 2502, 4320), (Sum.inr 2506, 4320), (Sum.inr 2513, 4320), (Sum.inr 2681, 4320), (Sum.inr 2683, 2160), (Sum.inr 2687, 2160), (Sum.inr 2735, 4320), (Sum.inr 2737, 2160), (Sum.inr 2744, 2160), (Sum.inr 2773, 4320), (Sum.inr 2774, 2160), (Sum.inr 3572, 4320), (Sum.inr 3582, 2160), (Sum.inr 3583, 2160)]

def numericRow373 : Integer.Sparse Master := [(Sum.inr 2769, 1), (Sum.inr 3051, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def numericRow374 : Integer.Sparse Master := [(Sum.inr 1268, 2), (Sum.inr 1272, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def numericRow375 : Integer.Sparse Master := [(Sum.inr 1268, 1), (Sum.inr 2571, 1), (Sum.inr 2639, 1), (Sum.inr 2759, 1), (Sum.inr 2763, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def numericRow376 : Integer.Sparse Master := [(Sum.inr 1433, 1), (Sum.inr 2571, 1), (Sum.inr 2575, 1), (Sum.inr 2600, 1), (Sum.inr 2769, 1), (Sum.inr 3051, 1), (Sum.inr 4092, -1)]

def numericRow377 : Integer.Sparse Master := [(Sum.inr 1437, 1), (Sum.inr 2639, 2), (Sum.inr 2643, 1), (Sum.inr 2769, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def numericRow378 : Integer.Sparse Master := [(Sum.inr 1273, 1), (Sum.inr 2575, 2), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def numericRow379 : Integer.Sparse Master := [(Sum.inr 1272, 1), (Sum.inr 1433, 2), (Sum.inr 1436, 1), (Sum.inr 1437, 1), (Sum.inr 2769, 1), (Sum.inr 4092, -1)]

def numericRow380 : Integer.Sparse Master := [(Sum.inl 0, -64), (Sum.inl 2, -40), (Sum.inl 3, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -200), (Sum.inr 1656, 8640), (Sum.inr 1657, 4320), (Sum.inr 1661, 4320), (Sum.inr 1745, 4320), (Sum.inr 2259, 8640), (Sum.inr 2287, 4320), (Sum.inr 2290, 4320), (Sum.inr 2584, 8640), (Sum.inr 2603, 4320), (Sum.inr 2717, 8640), (Sum.inr 2735, 8640), (Sum.inr 2738, 8640), (Sum.inr 2761, 4320), (Sum.inr 2762, 8640), (Sum.inr 2763, 8640), (Sum.inr 2781, 4320), (Sum.inr 2782, 4320), (Sum.inr 3096, 8640), (Sum.inr 3118, 4320)]

def numericRow381 : Integer.Sparse Master := [(Sum.inr 3098, 1), (Sum.inr 3572, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def numericRow382 : Integer.Sparse Master := [(Sum.inr 1404, 2), (Sum.inr 1408, 1), (Sum.inr 1418, 1), (Sum.inr 1440, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def numericRow383 : Integer.Sparse Master := [(Sum.inr 1404, 1), (Sum.inr 2952, 1), (Sum.inr 2983, 1), (Sum.inr 3075, 1), (Sum.inr 3096, 1), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow384 : Integer.Sparse Master := [(Sum.inr 2090, 1), (Sum.inr 2962, 1), (Sum.inr 2983, 1), (Sum.inr 2995, 1), (Sum.inr 3098, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def numericRow385 : Integer.Sparse Master := [(Sum.inr 1440, 1), (Sum.inr 2995, 2), (Sum.inr 3098, 2), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

def numericRow386 : Integer.Sparse Master := [(Sum.inr 2112, 1), (Sum.inr 2952, 2), (Sum.inr 2967, 1), (Sum.inr 3098, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def numericRow387 : Integer.Sparse Master := [(Sum.inr 1418, 1), (Sum.inr 2962, 2), (Sum.inr 2967, 2), (Sum.inr 3098, 1), (Sum.inr 4083, -1)]

def numericRow388 : Integer.Sparse Master := [(Sum.inl 0, -49), (Sum.inl 2, 80), (Sum.inl 3, -80), (Sum.inl 13, 80), (Sum.inl 1, 65), (Sum.inr 2516, 4320), (Sum.inr 2520, 2160), (Sum.inr 2521, 2160), (Sum.inr 2719, 4320), (Sum.inr 2737, 2160), (Sum.inr 2740, 2160), (Sum.inr 2783, 2160), (Sum.inr 2789, 2160), (Sum.inr 3035, 4320), (Sum.inr 3049, 2160), (Sum.inr 3052, 2160), (Sum.inr 3063, 4320), (Sum.inr 3072, 4320), (Sum.inr 3075, 4320), (Sum.inr 3086, 4320), (Sum.inr 3098, 4320), (Sum.inr 3158, 4320), (Sum.inr 3161, 2160)]

def numericRow389 : Integer.Sparse Master := [(Sum.inr 1292, 1), (Sum.inr 2588, 2), (Sum.inr 2740, 1), (Sum.inr 2781, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

def numericRow390 : Integer.Sparse Master := [(Sum.inr 2132, 2), (Sum.inr 2134, 1), (Sum.inr 2138, 1), (Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 4084, -1)]

def numericRow391 : Integer.Sparse Master := [(Sum.inl 0, -124), (Sum.inl 3, 640), (Sum.inl 12, 320), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -100), (Sum.inr 1189, 8640), (Sum.inr 1191, 4320), (Sum.inr 1192, 4320), (Sum.inr 1295, 4320), (Sum.inr 2393, 8640), (Sum.inr 2408, 4320), (Sum.inr 2734, 4320), (Sum.inr 2841, 8640), (Sum.inr 2842, 4320), (Sum.inr 2909, 8640), (Sum.inr 2910, 8640), (Sum.inr 2955, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3052, 4320), (Sum.inr 3584, 4320), (Sum.inr 3877, 8640)]

def numericRow392 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 2405, 2160), (Sum.inr 2408, 1080), (Sum.inr 2409, 1080), (Sum.inr 2744, 1080), (Sum.inr 2841, 2160), (Sum.inr 2842, 1080), (Sum.inr 3055, 1080), (Sum.inr 3246, 2160), (Sum.inr 3247, 1080), (Sum.inr 3306, 1080), (Sum.inr 3358, 2160), (Sum.inr 3535, 2160), (Sum.inr 3548, 1080), (Sum.inr 3549, 1080), (Sum.inr 3559, 2160), (Sum.inr 3565, 2160), (Sum.inr 3573, 2160), (Sum.inr 3583, 1080), (Sum.inr 3877, 2160)]

def numericRow393 : Integer.Sparse Master := [(Sum.inr 2774, 2), (Sum.inr 3854, 2), (Sum.inr 3907, 2), (Sum.inr 4092, -1)]

def numericRow394 : Integer.Sparse Master := [(Sum.inr 1295, 1), (Sum.inr 2591, 2), (Sum.inr 2743, 1), (Sum.inr 2774, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def numericRow395 : Integer.Sparse Master := [(Sum.inl 0, -240), (Sum.inl 5, 80), (Sum.inl 2, -80), (Sum.inl 51, -960), (Sum.inl 3, 640), (Sum.inl 13, 320), (Sum.inl 12, 320), (Sum.inl 4, 320), (Sum.inl 1, 80), (Sum.inl 31, -960), (Sum.inr 1054, 17280), (Sum.inr 1055, 8640), (Sum.inr 1063, 8640), (Sum.inr 1076, 8640), (Sum.inr 2491, 17280), (Sum.inr 2492, 17280), (Sum.inr 2499, 17280), (Sum.inr 2506, 17280), (Sum.inr 2633, 17280), (Sum.inr 2635, 8640), (Sum.inr 2678, 17280), (Sum.inr 2680, 8640), (Sum.inr 2687, 8640), (Sum.inr 2773, 17280), (Sum.inr 2781, 8640), (Sum.inr 3881, 17280), (Sum.inr 3886, 8640)]

def numericRow396 : Integer.Sparse Master := [(Sum.inl 0, -28), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inl 25, -240), (Sum.inl 4, 80), (Sum.inl 1, -15), (Sum.inr 1649, 4320), (Sum.inr 1651, 2160), (Sum.inr 1652, 2160), (Sum.inr 1740, 2160), (Sum.inr 2875, 4320), (Sum.inr 2888, 2160), (Sum.inr 3098, 2160), (Sum.inr 3385, 4320), (Sum.inr 3395, 4320), (Sum.inr 3396, 2160), (Sum.inr 3447, 4320), (Sum.inr 3480, 4320), (Sum.inr 3573, 4320), (Sum.inr 3578, 4320), (Sum.inr 3579, 2160), (Sum.inr 3626, 2160), (Sum.inr 3631, 2160), (Sum.inr 3959, 4320), (Sum.inr 3963, 2160)]

def numericRow397 : Integer.Sparse Master := [(Sum.inr 3055, 1), (Sum.inr 3884, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

def numericRow398 : Integer.Sparse Master := [(Sum.inr 1368, 2), (Sum.inr 1373, 1), (Sum.inr 1375, 1), (Sum.inr 1437, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def numericRow399 : Integer.Sparse Master := [(Sum.inr 1368, 1), (Sum.inr 2882, 1), (Sum.inr 2975, 1), (Sum.inr 3044, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow400 : Integer.Sparse Master := [(Sum.inr 2639, 1), (Sum.inr 2871, 1), (Sum.inr 2975, 1), (Sum.inr 2979, 1), (Sum.inr 3055, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def numericRow401 : Integer.Sparse Master := [(Sum.inr 2882, 2), (Sum.inr 2886, 1), (Sum.inr 2889, 1), (Sum.inr 3055, 1), (Sum.inr 3963, 1), (Sum.inr 4092, -1)]

def numericRow402 : Integer.Sparse Master := [(Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

def numericRow403 : Integer.Sparse Master := [(Sum.inr 2643, 1), (Sum.inr 3044, 2), (Sum.inr 3046, 1), (Sum.inr 3055, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

def numericRow404 : Integer.Sparse Master := [(Sum.inl 0, -138), (Sum.inl 2, 160), (Sum.inl 3, 320), (Sum.inl 13, 160), (Sum.inl 55, -480), (Sum.inl 12, 160), (Sum.inl 27, -120), (Sum.inl 1, 130), (Sum.inr 2129, 8640), (Sum.inr 2130, 4320), (Sum.inr 2138, 4320), (Sum.inr 2251, 8640), (Sum.inr 2276, 4320), (Sum.inr 2278, 4320), (Sum.inr 2282, 4320), (Sum.inr 2629, 8640), (Sum.inr 2643, 4320), (Sum.inr 2713, 8640), (Sum.inr 2729, 8640), (Sum.inr 2731, 8640), (Sum.inr 2751, 8640), (Sum.inr 2758, 8640), (Sum.inr 2765, 4320), (Sum.inr 2771, 4320), (Sum.inr 3092, 8640)]

def numericRow405 : Integer.Sparse Master := [(Sum.inr 2888, 1), (Sum.inr 3392, 2), (Sum.inr 3397, 1), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow406 : Integer.Sparse Master := [(Sum.inr 2108, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 2266, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow407 : Integer.Sparse Master := [(Sum.inr 2108, 1), (Sum.inr 2883, 1), (Sum.inr 3504, 1), (Sum.inr 3577, 1), (Sum.inr 3580, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow408 : Integer.Sparse Master := [(Sum.inr 2113, 1), (Sum.inr 2887, 1), (Sum.inr 3157, 2), (Sum.inr 3161, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow409 : Integer.Sparse Master := [(Sum.inr 2883, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 3056, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow410 : Integer.Sparse Master := [(Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 3506, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

def numericRow411 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -80), (Sum.inl 4, -80), (Sum.inl 1, 25), (Sum.inr 2519, -2160), (Sum.inr 2881, -4320), (Sum.inr 2889, -2160), (Sum.inr 3486, -2160), (Sum.inr 3624, -4320), (Sum.inr 3631, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160), (Sum.inr 4475, 17280), (Sum.inr 4476, 8640), (Sum.inr 4480, 8640), (Sum.inr 4500, 8640), (Sum.inr 5086, 17280), (Sum.inr 5087, 17280), (Sum.inr 5090, 17280), (Sum.inr 5103, 17280), (Sum.inr 5267, 17280), (Sum.inr 5268, 8640), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640), (Sum.inr 5299, 17280), (Sum.inr 5300, 8640)]

def numericRow412 : Integer.Sparse Master := [(Sum.inl 0, -55), (Sum.inl 2, -40), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 95), (Sum.inr 1058, 2160), (Sum.inr 1059, 1080), (Sum.inr 1063, 1080), (Sum.inr 1084, 1080), (Sum.inr 2494, 2160), (Sum.inr 2495, 2160), (Sum.inr 2499, 2160), (Sum.inr 2513, 2160), (Sum.inr 2732, 2160), (Sum.inr 2734, 1080), (Sum.inr 2744, 1080), (Sum.inr 2773, 2160), (Sum.inr 2774, 1080), (Sum.inr 2781, 1080)]

def numericRow413 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -25), (Sum.inr 1715, 4320), (Sum.inr 1716, 2160), (Sum.inr 1729, 2160), (Sum.inr 1740, 2160), (Sum.inr 3024, 4320), (Sum.inr 3052, 2160), (Sum.inr 3098, 2160), (Sum.inr 3464, 4320), (Sum.inr 3472, 4320), (Sum.inr 3480, 4320), (Sum.inr 3486, 2160), (Sum.inr 3541, 4320), (Sum.inr 3549, 2160), (Sum.inr 3573, 4320), (Sum.inr 3584, 2160), (Sum.inr 3624, 4320), (Sum.inr 3631, 2160), (Sum.inr 3809, 4320)]

def numericRow414 : Integer.Sparse Master := [(Sum.inr 3054, 1), (Sum.inr 3813, 2), (Sum.inr 3907, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def numericRow415 : Integer.Sparse Master := [(Sum.inr 1367, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1436, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow416 : Integer.Sparse Master := [(Sum.inr 2495, 1), (Sum.inr 2759, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 3054, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

def numericRow417 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2266, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 2522, -2160), (Sum.inr 2672, -4320), (Sum.inr 2685, -2160), (Sum.inr 2686, -2160), (Sum.inr 3077, -4320), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3625, -4320), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4880, 17280), (Sum.inr 4881, 8640), (Sum.inr 4884, 8640), (Sum.inr 4891, 17280), (Sum.inr 4892, 8640), (Sum.inr 5103, 17280), (Sum.inr 5254, 17280), (Sum.inr 5266, 17280), (Sum.inr 5267, 17280), (Sum.inr 5276, 8640), (Sum.inr 5287, 17280), (Sum.inr 5300, 8640)]

def numericRow418 : Integer.Sparse Master := [(Sum.inl 0, -70), (Sum.inl 2, 125), (Sum.inl 3, 160), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 95), (Sum.inr 2254, 4320), (Sum.inr 2255, 2160), (Sum.inr 2267, 2160), (Sum.inr 2280, 2160), (Sum.inr 2672, 4320), (Sum.inr 2685, 2160), (Sum.inr 2686, 2160), (Sum.inr 3016, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3038, 4320), (Sum.inr 3039, 4320), (Sum.inr 3052, 2160), (Sum.inr 3055, 2160), (Sum.inr 3077, 4320), (Sum.inr 3222, 4320)]

def numericRow419 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 15), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 4, -160), (Sum.inl 1, -90), (Sum.inr 2396, 4320), (Sum.inr 2397, 4320), (Sum.inr 2401, 8640), (Sum.inr 2738, 4320), (Sum.inr 3282, 4320), (Sum.inr 3283, 4320), (Sum.inr 3294, 8640), (Sum.inr 3350, 4320), (Sum.inr 3355, 8640), (Sum.inr 3543, 4320), (Sum.inr 3544, 8640), (Sum.inr 3562, 8640), (Sum.inr 3568, 8640), (Sum.inr 3571, 4320), (Sum.inr 3578, 8640), (Sum.inr 3581, 8640), (Sum.inr 3874, 4320), (Sum.inr 3884, 8640)]

def numericRow420 : Integer.Sparse Master := [(Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 3881, 2), (Sum.inr 3902, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

def numericRow421 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1249, 1), (Sum.inr 1253, 1), (Sum.inr 1262, 2), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

def numericRow422 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 2564, 1), (Sum.inr 2567, 2), (Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

def numericRow423 : Integer.Sparse Master := [(Sum.inr 1262, 1), (Sum.inr 2567, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 2751, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def numericRow424 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2624, 1), (Sum.inr 2627, 1), (Sum.inr 2633, 1), (Sum.inr 2751, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

def numericRow425 : Integer.Sparse Master := [(Sum.inr 1253, 1), (Sum.inr 2564, 1), (Sum.inr 2627, 2), (Sum.inr 2751, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def numericRow426 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2931, -8640), (Sum.inr 3077, -4320), (Sum.inr 3612, -8640), (Sum.inr 3625, -4320), (Sum.inr 3885, -8640), (Sum.inr 3958, -8640), (Sum.inr 3961, -8640), (Sum.inr 4010, -4320), (Sum.inr 4436, 17280), (Sum.inr 4437, 17280), (Sum.inr 4444, 17280), (Sum.inr 4453, 34560), (Sum.inr 5064, 17280), (Sum.inr 5067, 17280), (Sum.inr 5071, 34560), (Sum.inr 5145, 34560), (Sum.inr 5147, 34560), (Sum.inr 5164, 34560), (Sum.inr 5220, 17280), (Sum.inr 5222, 17280), (Sum.inr 5229, 34560), (Sum.inr 5281, 17280), (Sum.inr 5289, 34560)]

def numericRow427 : Integer.Sparse Master := [(Sum.inl 0, -334), (Sum.inl 5, 240), (Sum.inl 2, -160), (Sum.inl 7, -320), (Sum.inl 8, -320), (Sum.inl 51, 960), (Sum.inl 3, -1120), (Sum.inl 13, -160), (Sum.inl 12, -160), (Sum.inl 4, -640), (Sum.inl 1, 190), (Sum.inl 31, 960), (Sum.inr 1018, 8640), (Sum.inr 1019, 8640), (Sum.inr 1026, 8640), (Sum.inr 1036, 17280), (Sum.inr 2469, 8640), (Sum.inr 2473, 8640), (Sum.inr 2478, 17280), (Sum.inr 2567, 17280), (Sum.inr 2569, 17280), (Sum.inr 2591, 17280), (Sum.inr 2662, 8640), (Sum.inr 2664, 8640), (Sum.inr 2673, 17280), (Sum.inr 2750, 8640), (Sum.inr 2763, 17280), (Sum.inr 3885, 8640)]

def numericRow428 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 25), (Sum.inl 3, -240), (Sum.inl 12, -160), (Sum.inl 25, 240), (Sum.inl 4, -160), (Sum.inl 1, -50), (Sum.inr 1642, 4320), (Sum.inr 1643, 4320), (Sum.inr 1646, 8640), (Sum.inr 1736, 4320), (Sum.inr 3388, 4320), (Sum.inr 3389, 4320), (Sum.inr 3392, 8640), (Sum.inr 3443, 4320), (Sum.inr 3445, 8640), (Sum.inr 3476, 4320), (Sum.inr 3530, 8640), (Sum.inr 3562, 8640), (Sum.inr 3565, 8640), (Sum.inr 3571, 4320), (Sum.inr 3572, 8640), (Sum.inr 3612, 8640), (Sum.inr 3625, 4320), (Sum.inr 3961, 8640)]

def numericRow429 : Integer.Sparse Master := [(Sum.inr 3078, 1), (Sum.inr 3885, 1), (Sum.inr 3958, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def numericRow430 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 1389, 1), (Sum.inr 1391, 1), (Sum.inr 1407, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def numericRow431 : Integer.Sparse Master := [(Sum.inr 1384, 1), (Sum.inr 2925, 2), (Sum.inr 3068, 1), (Sum.inr 3074, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow432 : Integer.Sparse Master := [(Sum.inr 2857, 1), (Sum.inr 2981, 1), (Sum.inr 2985, 2), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def numericRow433 : Integer.Sparse Master := [(Sum.inr 1407, 1), (Sum.inr 2955, 1), (Sum.inr 2985, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def numericRow434 : Integer.Sparse Master := [(Sum.inr 2865, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 2955, 1), (Sum.inr 3078, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

def numericRow435 : Integer.Sparse Master := [(Sum.inr 1391, 1), (Sum.inr 2931, 2), (Sum.inr 2981, 1), (Sum.inr 3077, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def numericRow436 : Integer.Sparse Master := [(Sum.inr 3031, 1), (Sum.inr 3068, 1), (Sum.inr 3078, 1), (Sum.inr 3092, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

def numericRow437 : Integer.Sparse Master := [(Sum.inr 1389, 1), (Sum.inr 2857, 1), (Sum.inr 2865, 2), (Sum.inr 3031, 1), (Sum.inr 3078, 1), (Sum.inr 4091, -1)]

def numericRow438 : Integer.Sparse Master := [(Sum.inl 0, -456), (Sum.inl 2, 590), (Sum.inl 3, 160), (Sum.inl 13, -160), (Sum.inl 55, 480), (Sum.inl 12, -160), (Sum.inl 27, 120), (Sum.inl 1, 710), (Sum.inr 2232, 8640), (Sum.inr 2242, 8640), (Sum.inr 2244, 8640), (Sum.inr 2251, 17280), (Sum.inr 2628, 8640), (Sum.inr 2629, 17280), (Sum.inr 2641, 8640), (Sum.inr 2708, 8640), (Sum.inr 2713, 17280), (Sum.inr 2745, 8640), (Sum.inr 2748, 8640), (Sum.inr 2751, 17280), (Sum.inr 2758, 17280), (Sum.inr 2765, 17280), (Sum.inr 2774, 17280)]

def numericRow439 : Integer.Sparse Master := [(Sum.inr 2879, 1), (Sum.inr 3498, 1), (Sum.inr 3548, 2), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def numericRow440 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 2), (Sum.inr 2262, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def numericRow441 : Integer.Sparse Master := [(Sum.inr 2104, 1), (Sum.inr 2877, 1), (Sum.inr 3576, 1), (Sum.inr 3580, 3), (Sum.inr 4084, -1)]

def numericRow442 : Integer.Sparse Master := [(Sum.inr 2877, 1), (Sum.inr 2879, 1), (Sum.inr 2883, 2), (Sum.inr 3050, 1), (Sum.inr 3580, 1), (Sum.inr 4084, -1)]

def numericRow443 : Integer.Sparse Master := [(Sum.inr 2106, 1), (Sum.inr 3050, 1), (Sum.inr 3502, 1), (Sum.inr 3580, 1), (Sum.inr 3582, 2), (Sum.inr 4084, -1)]

def numericRow444 : Integer.Sparse Master := [(Sum.inl 0, 195), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -130), (Sum.inr 1200, -2160), (Sum.inr 1202, -2160), (Sum.inr 1205, -2160), (Sum.inr 1236, -4320), (Sum.inr 1898, -2160), (Sum.inr 1915, -4320), (Sum.inr 1940, -2160), (Sum.inr 1942, -2160), (Sum.inr 1946, -4320), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2853, -4320), (Sum.inr 2856, -4320), (Sum.inr 2881, -4320), (Sum.inr 2913, -2160), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3281, -2160), (Sum.inr 3284, -2160), (Sum.inr 3293, -4320), (Sum.inr 3605, -4320), (Sum.inr 3610, -2160), (Sum.inr 3620, -4320), (Sum.inr 3622, -4320), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3630, -4320), (Sum.inr 3632, -4320), (Sum.inr 3801, -2160), (Sum.inr 3809, -4320), (Sum.inr 3812, -2160), (Sum.inr 3813, -4320)]

def numericRow445 : Integer.Sparse Master := [(Sum.inl 0, -140), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 1, 115), (Sum.inr 1200, 2160), (Sum.inr 1202, 2160), (Sum.inr 1205, 2160), (Sum.inr 1236, 4320), (Sum.inr 1898, 2160), (Sum.inr 1915, 4320), (Sum.inr 2247, 2160), (Sum.inr 2853, 4320), (Sum.inr 2856, 4320), (Sum.inr 2881, 4320), (Sum.inr 2913, 2160), (Sum.inr 2924, 4320), (Sum.inr 3077, 4320), (Sum.inr 3801, 2160), (Sum.inr 3809, 4320)]

def numericRow446 : Integer.Sparse Master := [(Sum.inl 0, 41), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, 70), (Sum.inr 2485, -4320), (Sum.inr 2924, -4320), (Sum.inr 2931, -4320), (Sum.inr 2954, -4320), (Sum.inr 3481, -4320), (Sum.inr 3605, -4320), (Sum.inr 3606, -4320), (Sum.inr 3612, -4320), (Sum.inr 3800, -2160), (Sum.inr 3805, -2160), (Sum.inr 3902, -2160), (Sum.inr 4010, -2160), (Sum.inr 4439, 8640), (Sum.inr 4440, 8640), (Sum.inr 4444, 8640), (Sum.inr 4459, 17280), (Sum.inr 5065, 8640), (Sum.inr 5067, 8640), (Sum.inr 5074, 17280), (Sum.inr 5251, 8640), (Sum.inr 5252, 8640), (Sum.inr 5260, 17280), (Sum.inr 5281, 8640), (Sum.inr 5282, 8640), (Sum.inr 5289, 17280)]

def numericRow447 : Integer.Sparse Master := [(Sum.inl 0, -78), (Sum.inl 2, 35), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, -235), (Sum.inr 1021, 1440), (Sum.inr 1022, 1440), (Sum.inr 1026, 1440), (Sum.inr 1042, 2880), (Sum.inr 2470, 1440), (Sum.inr 2473, 1440), (Sum.inr 2481, 2880), (Sum.inr 2710, 1440), (Sum.inr 2712, 1440), (Sum.inr 2724, 2880), (Sum.inr 2750, 1440), (Sum.inr 2751, 1440), (Sum.inr 2763, 2880)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow448 : Integer.Sparse Master := [(Sum.inl 0, -41), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, -70), (Sum.inr 1713, 2160), (Sum.inr 1714, 4320), (Sum.inr 1723, 2160), (Sum.inr 1736, 2160), (Sum.inr 3463, 4320), (Sum.inr 3466, 2160), (Sum.inr 3476, 2160), (Sum.inr 3481, 4320), (Sum.inr 3539, 2160), (Sum.inr 3540, 4320), (Sum.inr 3543, 2160), (Sum.inr 3571, 2160), (Sum.inr 3572, 4320), (Sum.inr 3580, 2160), (Sum.inr 3605, 4320), (Sum.inr 3606, 4320), (Sum.inr 3612, 4320), (Sum.inr 3805, 2160)]

def numericRow449 : Integer.Sparse Master := [(Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 3902, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def numericRow450 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1406, 2), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

def numericRow451 : Integer.Sparse Master := [(Sum.inr 2470, 1), (Sum.inr 2981, 1), (Sum.inr 2984, 2), (Sum.inr 3077, 1), (Sum.inr 3800, 1), (Sum.inr 4091, -1)]

def numericRow452 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2244, -1080), (Sum.inr 2245, -1080), (Sum.inr 2262, -1080), (Sum.inr 2277, -1080), (Sum.inr 2509, -1080), (Sum.inr 2694, -1080), (Sum.inr 2704, -1080), (Sum.inr 2705, -1080), (Sum.inr 3054, -2160), (Sum.inr 3077, -2160), (Sum.inr 3493, -1080), (Sum.inr 3498, -1080), (Sum.inr 3625, -2160), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4885, 4320), (Sum.inr 4891, 8640), (Sum.inr 5097, 4320), (Sum.inr 5103, 8640), (Sum.inr 5251, 4320), (Sum.inr 5254, 8640), (Sum.inr 5270, 4320), (Sum.inr 5277, 4320), (Sum.inr 5282, 4320), (Sum.inr 5287, 8640)]

def numericRow453 : Integer.Sparse Master := [(Sum.inl 0, -126), (Sum.inl 2, 155), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, 125), (Sum.inr 2233, 1440), (Sum.inr 2244, 1440), (Sum.inr 2245, 1440), (Sum.inr 2253, 2880), (Sum.inr 2710, 1440), (Sum.inr 2714, 2880), (Sum.inr 2745, 1440), (Sum.inr 2746, 1440), (Sum.inr 2751, 1440), (Sum.inr 2754, 1440), (Sum.inr 2758, 2880), (Sum.inr 2759, 2880)]

def numericRow454 : Integer.Sparse Master := [(Sum.inl 0, -231), (Sum.inl 2, 235), (Sum.inl 3, 80), (Sum.inl 13, -320), (Sum.inl 12, -80), (Sum.inl 1, 310), (Sum.inr 2694, 4320), (Sum.inr 2704, 4320), (Sum.inr 2705, 4320), (Sum.inr 3016, 8640), (Sum.inr 3024, 8640), (Sum.inr 3025, 8640), (Sum.inr 3054, 8640), (Sum.inr 3058, 4320), (Sum.inr 3059, 4320), (Sum.inr 3064, 4320), (Sum.inr 3075, 4320), (Sum.inr 3077, 8640), (Sum.inr 3078, 4320), (Sum.inr 3221, 4320), (Sum.inr 3222, 8640)]

def numericRow455 : Integer.Sparse Master := [(Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 3498, 1), (Sum.inr 3625, 1), (Sum.inr 4084, -1)]

def numericRow456 : Integer.Sparse Master := [(Sum.inl 0, -45), (Sum.inl 2, -5), (Sum.inl 3, -400), (Sum.inl 13, -160), (Sum.inl 12, -320), (Sum.inl 4, -160), (Sum.inl 1, -20), (Sum.inr 995, 4320), (Sum.inr 997, 4320), (Sum.inr 1001, 8640), (Sum.inr 1078, 4320), (Sum.inr 2396, 4320), (Sum.inr 2397, 4320), (Sum.inr 2401, 8640), (Sum.inr 2457, 4320), (Sum.inr 2460, 8640), (Sum.inr 2507, 4320), (Sum.inr 2700, 8640), (Sum.inr 2702, 8640), (Sum.inr 2706, 8640), (Sum.inr 2730, 4320), (Sum.inr 2731, 8640), (Sum.inr 2738, 8640), (Sum.inr 3571, 4320), (Sum.inr 3580, 4320), (Sum.inr 3581, 8640)]

def numericRow457 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 1252, 1), (Sum.inr 1253, 1), (Sum.inr 1270, 2), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def numericRow458 : Integer.Sparse Master := [(Sum.inr 1250, 1), (Sum.inr 2625, 2), (Sum.inr 2746, 1), (Sum.inr 2750, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

def numericRow459 : Integer.Sparse Master := [(Sum.inr 1421, 1), (Sum.inr 2564, 1), (Sum.inr 2573, 2), (Sum.inr 2754, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

def numericRow460 : Integer.Sparse Master := [(Sum.inr 1270, 1), (Sum.inr 2573, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 2), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

def numericRow461 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 2025, -4320), (Sum.inr 2224, -4320), (Sum.inr 2247, -2160), (Sum.inr 2290, -2160), (Sum.inr 2739, -4320), (Sum.inr 2764, -2160), (Sum.inr 3534, -4320), (Sum.inr 3581, -2160), (Sum.inr 3623, -2160), (Sum.inr 4441, 8640), (Sum.inr 4442, 8640), (Sum.inr 4443, 8640), (Sum.inr 4462, 17280), (Sum.inr 4792, 8640), (Sum.inr 5066, 8640), (Sum.inr 5077, 17280), (Sum.inr 5150, 17280), (Sum.inr 5151, 17280), (Sum.inr 5173, 17280), (Sum.inr 5270, 8640), (Sum.inr 5278, 8640), (Sum.inr 5279, 8640), (Sum.inr 5288, 17280), (Sum.inr 5295, 17280)]

def numericRow462 : Integer.Sparse Master := [(Sum.inl 0, -376), (Sum.inl 5, 80), (Sum.inl 6, -60), (Sum.inl 2, -500), (Sum.inl 35, -320), (Sum.inl 3, -640), (Sum.inl 13, -320), (Sum.inl 52, -320), (Sum.inl 26, -320), (Sum.inl 4, -320), (Sum.inl 1, -480), (Sum.inr 1023, 8640), (Sum.inr 1024, 8640), (Sum.inr 1025, 8640), (Sum.inr 1045, 17280), (Sum.inr 2471, 8640), (Sum.inr 2472, 8640), (Sum.inr 2484, 17280), (Sum.inr 2573, 17280), (Sum.inr 2575, 17280), (Sum.inr 2600, 17280), (Sum.inr 2747, 8640), (Sum.inr 2748, 8640), (Sum.inr 2754, 8640), (Sum.inr 2760, 17280), (Sum.inr 2764, 8640), (Sum.inr 2769, 17280)]

def numericRow463 : Integer.Sparse Master := [(Sum.inl 0, -59), (Sum.inl 2, -35), (Sum.inl 3, -80), (Sum.inl 26, -160), (Sum.inl 4, -160), (Sum.inl 1, -220), (Sum.inr 1654, 4320), (Sum.inr 1655, 4320), (Sum.inr 1656, 8640), (Sum.inr 1744, 4320), (Sum.inr 2201, 4320), (Sum.inr 2224, 8640), (Sum.inr 2290, 4320), (Sum.inr 2668, 4320), (Sum.inr 2681, 8640), (Sum.inr 2700, 8640), (Sum.inr 2717, 8640), (Sum.inr 2735, 8640), (Sum.inr 2738, 4320), (Sum.inr 2739, 8640), (Sum.inr 2781, 8640), (Sum.inr 3050, 4320), (Sum.inr 3073, 4320), (Sum.inr 3096, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow464 : Integer.Sparse Master := [(Sum.inr 3075, 1), (Sum.inr 3534, 2), (Sum.inr 3581, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def numericRow465 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 1385, 1), (Sum.inr 1390, 1), (Sum.inr 1404, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

def numericRow466 : Integer.Sparse Master := [(Sum.inr 1382, 1), (Sum.inr 2923, 2), (Sum.inr 3073, 1), (Sum.inr 3075, 2), (Sum.inr 4083, -1)]

def numericRow467 : Integer.Sparse Master := [(Sum.inr 2009, 1), (Sum.inr 2980, 1), (Sum.inr 2983, 2), (Sum.inr 3075, 1), (Sum.inr 4083, -1)]

def numericRow468 : Integer.Sparse Master := [(Sum.inr 2025, 1), (Sum.inr 2923, 1), (Sum.inr 2930, 1), (Sum.inr 2952, 1), (Sum.inr 3075, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

def numericRow469 : Integer.Sparse Master := [(Sum.inr 1390, 1), (Sum.inr 2930, 2), (Sum.inr 2980, 1), (Sum.inr 3075, 1), (Sum.inr 3079, 1), (Sum.inr 4083, -1)]

def numericRow470 : Integer.Sparse Master := [(Sum.inl 0, -102), (Sum.inl 2, 95), (Sum.inl 3, 160), (Sum.inl 13, -240), (Sum.inl 12, -80), (Sum.inl 1, 185), (Sum.inr 2702, 4320), (Sum.inr 2704, 4320), (Sum.inr 2740, 8640), (Sum.inr 3015, 8640), (Sum.inr 3022, 8640), (Sum.inr 3024, 8640), (Sum.inr 3052, 8640), (Sum.inr 3057, 4320), (Sum.inr 3058, 4320), (Sum.inr 3063, 4320), (Sum.inr 3064, 4320), (Sum.inr 3072, 4320), (Sum.inr 3075, 8640), (Sum.inr 3077, 4320), (Sum.inr 3098, 8640), (Sum.inr 3155, 4320), (Sum.inr 3156, 8640), (Sum.inr 3158, 4320)]

def numericRow471 : Integer.Sparse Master := [(Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 2738, 1), (Sum.inr 2740, 2), (Sum.inr 4084, -1)]

def numericRow472 : Integer.Sparse Master := [(Sum.inr 2131, 1), (Sum.inr 2132, 1), (Sum.inr 2133, 2), (Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 4084, -1)]

def numericRow473 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 1294, -2160), (Sum.inr 2590, -4320), (Sum.inr 2722, -4320), (Sum.inr 2726, -2160), (Sum.inr 2782, -2160), (Sum.inr 3305, -2160), (Sum.inr 3533, -4320), (Sum.inr 3545, -2160), (Sum.inr 3564, -4320), (Sum.inr 3583, -2160), (Sum.inr 3850, -8640), (Sum.inr 3886, -4320), (Sum.inr 3913, -2160), (Sum.inr 4607, 17280), (Sum.inr 4609, 8640), (Sum.inr 4611, 8640), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5151, 17280), (Sum.inr 5198, 17280), (Sum.inr 5201, 8640), (Sum.inr 5206, 8640), (Sum.inr 5289, 17280), (Sum.inr 5295, 8640)]

def numericRow474 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 2, -90), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 1, 70), (Sum.inr 1241, 2880), (Sum.inr 1243, 1440), (Sum.inr 1245, 1440), (Sum.inr 2865, 2880), (Sum.inr 2885, 2880), (Sum.inr 2886, 1440), (Sum.inr 2888, 1440), (Sum.inr 2928, 2880), (Sum.inr 2930, 2880), (Sum.inr 3097, 2880), (Sum.inr 3098, 1440)]

def numericRow475 : Integer.Sparse Master := [(Sum.inl 0, -18), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, 25), (Sum.inr 2681, 4320), (Sum.inr 2683, 2160), (Sum.inr 2687, 2160), (Sum.inr 2781, 2160), (Sum.inr 3296, 4320), (Sum.inr 3302, 2160), (Sum.inr 3305, 2160), (Sum.inr 3530, 4320), (Sum.inr 3533, 4320), (Sum.inr 3545, 2160), (Sum.inr 3557, 4320), (Sum.inr 3564, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3579, 2160), (Sum.inr 3583, 2160), (Sum.inr 3850, 4320), (Sum.inr 3886, 2160)]

def numericRow476 : Integer.Sparse Master := [(Sum.inr 2765, 1), (Sum.inr 3850, 2), (Sum.inr 3886, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def numericRow477 : Integer.Sparse Master := [(Sum.inr 1261, 2), (Sum.inr 1264, 1), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def numericRow478 : Integer.Sparse Master := [(Sum.inr 1294, 1), (Sum.inr 2590, 2), (Sum.inr 2765, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def numericRow479 : Integer.Sparse Master := [(Sum.inr 2632, 2), (Sum.inr 2635, 1), (Sum.inr 2643, 1), (Sum.inr 2765, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow48 : Integer.Sparse Master := [(Sum.inr 2040, 1), (Sum.inr 2041, 1), (Sum.inr 2042, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

def numericRow49 : Integer.Sparse Master := [(Sum.inr 1068, 2), (Sum.inr 2042, 2), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

def numericRow50 : Integer.Sparse Master := [(Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 3158, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

def numericRow51 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1016, 1), (Sum.inr 1024, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def numericRow52 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 2083, 3), (Sum.inr 2233, 1), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def numericRow53 : Integer.Sparse Master := [(Sum.inr 1457, 1), (Sum.inr 2010, 3), (Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 4083, -1)]

def numericRow54 : Integer.Sparse Master := [(Sum.inr 1024, 1), (Sum.inr 2010, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

def numericRow55 : Integer.Sparse Master := [(Sum.inr 1460, 1), (Sum.inr 2083, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 3158, 1), (Sum.inr 4083, -1)]

def numericRow56 : Integer.Sparse Master := [(Sum.inr 1016, 1), (Sum.inr 1457, 1), (Sum.inr 1460, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

def numericRow57 : Integer.Sparse Master := [(Sum.inr 1078, 1), (Sum.inr 2050, 1), (Sum.inr 2283, 1), (Sum.inr 2290, 3), (Sum.inr 4085, -1)]

def numericRow58 : Integer.Sparse Master := [(Sum.inl 0, -236), (Sum.inl 6, -20), (Sum.inl 2, 180), (Sum.inl 3, 1280), (Sum.inl 13, 320), (Sum.inl 52, 320), (Sum.inl 12, 640), (Sum.inl 1, -60), (Sum.inr 991, 17280), (Sum.inr 994, 8640), (Sum.inr 1010, 8640), (Sum.inr 1059, 8640), (Sum.inr 1181, 17280), (Sum.inr 1191, 8640), (Sum.inr 1264, 8640), (Sum.inr 2393, 17280), (Sum.inr 2408, 8640), (Sum.inr 2454, 17280), (Sum.inr 2465, 17280), (Sum.inr 2495, 17280), (Sum.inr 2618, 17280), (Sum.inr 2732, 17280), (Sum.inr 2744, 8640), (Sum.inr 3039, 17280), (Sum.inr 3055, 8640)]

def numericRow59 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 1624, 4320), (Sum.inr 1628, 2160), (Sum.inr 1629, 2160), (Sum.inr 1729, 2160), (Sum.inr 2837, 4320), (Sum.inr 2842, 2160), (Sum.inr 3052, 2160), (Sum.inr 3242, 4320), (Sum.inr 3247, 2160), (Sum.inr 3302, 2160), (Sum.inr 3358, 4320), (Sum.inr 3437, 4320), (Sum.inr 3472, 4320), (Sum.inr 3486, 2160), (Sum.inr 3523, 4320), (Sum.inr 3535, 4320), (Sum.inr 3541, 4320), (Sum.inr 3548, 2160), (Sum.inr 3584, 2160), (Sum.inr 3626, 2160)]

def numericRow60 : Integer.Sparse Master := [(Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 3038, 2), (Sum.inr 3054, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

def numericRow61 : Integer.Sparse Master := [(Sum.inr 1224, 2), (Sum.inr 1227, 1), (Sum.inr 1243, 1), (Sum.inr 1279, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

def numericRow62 : Integer.Sparse Master := [(Sum.inr 1279, 1), (Sum.inr 2579, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

def numericRow63 : Integer.Sparse Master := [(Sum.inr 1372, 1), (Sum.inr 2495, 2), (Sum.inr 2519, 1), (Sum.inr 2734, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow480 : Integer.Sparse Master := [(Sum.inr 1261, 1), (Sum.inr 2566, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 2763, 1), (Sum.inr 2765, 1), (Sum.inr 4092, -1)]

def numericRow481 : Integer.Sparse Master := [(Sum.inl 0, 113), (Sum.inl 5, -20), (Sum.inl 2, -10), (Sum.inl 7, -80), (Sum.inl 3, -320), (Sum.inl 12, -80), (Sum.inl 4, -240), (Sum.inl 1, 25), (Sum.inr 1035, -4320), (Sum.inr 1037, -2160), (Sum.inr 1049, -2160), (Sum.inr 1075, -2160), (Sum.inr 1645, -4320), (Sum.inr 1647, -2160), (Sum.inr 1653, -2160), (Sum.inr 1738, -2160), (Sum.inr 2047, -4320), (Sum.inr 2065, -2160), (Sum.inr 2079, -4320), (Sum.inr 2109, -2160), (Sum.inr 2218, -2160), (Sum.inr 2261, -2160), (Sum.inr 2477, -4320), (Sum.inr 2488, -4320), (Sum.inr 2505, -4320), (Sum.inr 2590, -4320), (Sum.inr 2672, -4320), (Sum.inr 2686, -2160), (Sum.inr 2764, -4320), (Sum.inr 2782, -2160), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3444, -4320), (Sum.inr 3448, -4320), (Sum.inr 3478, -4320), (Sum.inr 3564, -4320), (Sum.inr 3581, -4320), (Sum.inr 3583, -2160), (Sum.inr 3614, -2160), (Sum.inr 3632, -2160), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160)]

def numericRow482 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 5, 4), (Sum.inl 2, 3), (Sum.inl 7, 16), (Sum.inl 3, 48), (Sum.inl 4, 32), (Sum.inl 1, 2), (Sum.inr 1035, 864), (Sum.inr 1037, 432), (Sum.inr 1049, 432), (Sum.inr 1075, 432), (Sum.inr 2079, 864), (Sum.inr 2109, 432), (Sum.inr 2218, 432), (Sum.inr 2477, 864), (Sum.inr 2488, 864), (Sum.inr 2505, 864), (Sum.inr 2590, 864), (Sum.inr 2672, 864), (Sum.inr 2686, 432), (Sum.inr 2764, 864), (Sum.inr 2782, 432), (Sum.inr 3876, 864), (Sum.inr 3907, 432)]

def numericRow483 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inr 2106, -1440), (Sum.inr 2109, -720), (Sum.inr 2115, -720), (Sum.inr 2242, -1440), (Sum.inr 2261, -720), (Sum.inr 2276, -720), (Sum.inr 2722, -1440), (Sum.inr 2743, -720), (Sum.inr 2765, -1440), (Sum.inr 2783, -1440), (Sum.inr 3533, -1440), (Sum.inr 3548, -720), (Sum.inr 3582, -1440), (Sum.inr 3627, -720), (Sum.inr 3633, -720), (Sum.inr 5161, 5760), (Sum.inr 5175, 2880), (Sum.inr 5249, 5760), (Sum.inr 5260, 5760), (Sum.inr 5264, 5760), (Sum.inr 5276, 2880), (Sum.inr 5279, 5760), (Sum.inr 5282, 5760), (Sum.inr 5297, 2880), (Sum.inr 5300, 2880)]

def numericRow484 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, 35), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 2242, 2160), (Sum.inr 2261, 1080), (Sum.inr 2276, 1080), (Sum.inr 2708, 2160), (Sum.inr 2719, 2160), (Sum.inr 2722, 2160), (Sum.inr 2729, 2160), (Sum.inr 2748, 2160), (Sum.inr 2751, 2160), (Sum.inr 2761, 1080), (Sum.inr 2765, 2160), (Sum.inr 2771, 1080), (Sum.inr 2774, 1080), (Sum.inr 2777, 1080), (Sum.inr 2783, 1080), (Sum.inr 3086, 2160)]

def numericRow485 : Integer.Sparse Master := [(Sum.inl 0, -116), (Sum.inl 2, 150), (Sum.inl 3, -160), (Sum.inl 26, -160), (Sum.inl 1, 130), (Sum.inr 2724, 2880), (Sum.inr 2743, 1440), (Sum.inr 2744, 1440), (Sum.inr 2964, 2880), (Sum.inr 2967, 1440), (Sum.inr 3040, 2880), (Sum.inr 3055, 1440), (Sum.inr 3056, 1440), (Sum.inr 3066, 2880), (Sum.inr 3078, 2880), (Sum.inr 3079, 2880)]

def numericRow486 : Integer.Sparse Master := [(Sum.inr 2106, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

def numericRow487 : Integer.Sparse Master := [(Sum.inl 0, 33), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, 190), (Sum.inr 1240, -4320), (Sum.inr 2480, -4320), (Sum.inr 2485, -4320), (Sum.inr 2489, -4320), (Sum.inr 2556, -4320), (Sum.inr 2721, -4320), (Sum.inr 2723, -8640), (Sum.inr 2764, -4320), (Sum.inr 3299, -4320), (Sum.inr 3467, -4320), (Sum.inr 3481, -4320), (Sum.inr 3482, -4320), (Sum.inr 3521, -4320), (Sum.inr 3532, -4320), (Sum.inr 3544, -8640), (Sum.inr 3581, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3902, -4320), (Sum.inr 4590, 17280), (Sum.inr 4591, 17280), (Sum.inr 4593, 17280), (Sum.inr 4603, 17280), (Sum.inr 5128, 17280), (Sum.inr 5139, 17280), (Sum.inr 5145, 17280), (Sum.inr 5185, 17280), (Sum.inr 5189, 17280), (Sum.inr 5199, 17280), (Sum.inr 5252, 17280), (Sum.inr 5282, 17280)]

def numericRow488 : Integer.Sparse Master := [(Sum.inl 0, -67), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, -200), (Sum.inr 1213, 1080), (Sum.inr 1215, 1080), (Sum.inr 1220, 1080), (Sum.inr 1237, 1080), (Sum.inr 2543, 1080), (Sum.inr 2558, 1080), (Sum.inr 2712, 1080), (Sum.inr 2862, 1080), (Sum.inr 2868, 1080), (Sum.inr 2882, 1080), (Sum.inr 2925, 1080), (Sum.inr 3078, 1080)]

def numericRow489 : Integer.Sparse Master := [(Sum.inl 0, -33), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, -190), (Sum.inr 3290, 4320), (Sum.inr 3291, 4320), (Sum.inr 3294, 4320), (Sum.inr 3297, 4320), (Sum.inr 3299, 4320), (Sum.inr 3467, 4320), (Sum.inr 3481, 4320), (Sum.inr 3482, 4320), (Sum.inr 3519, 4320), (Sum.inr 3521, 4320), (Sum.inr 3523, 4320), (Sum.inr 3529, 4320), (Sum.inr 3532, 4320), (Sum.inr 3542, 4320), (Sum.inr 3543, 4320), (Sum.inr 3544, 8640), (Sum.inr 3562, 4320), (Sum.inr 3578, 4320), (Sum.inr 3580, 4320), (Sum.inr 3581, 4320), (Sum.inr 3843, 4320), (Sum.inr 3857, 4320)]

def numericRow490 : Integer.Sparse Master := [(Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 3876, 1), (Sum.inr 3902, 1), (Sum.inr 4091, -1)]

def numericRow491 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1217, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

def numericRow492 : Integer.Sparse Master := [(Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

def numericRow493 : Integer.Sparse Master := [(Sum.inr 2615, 1), (Sum.inr 2618, 1), (Sum.inr 2621, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def numericRow494 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 1), (Sum.inr 2723, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

def numericRow495 : Integer.Sparse Master := [(Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 2489, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow496 : Integer.Sparse Master := [(Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 2621, 1), (Sum.inr 2723, 2), (Sum.inr 4091, -1)]

def numericRow497 : Integer.Sparse Master := [(Sum.inl 0, 438), (Sum.inl 6, -5), (Sum.inl 2, 55), (Sum.inl 8, 80), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, 170), (Sum.inr 980, -4320), (Sum.inr 982, -4320), (Sum.inr 985, -4320), (Sum.inr 1005, -4320), (Sum.inr 1041, -4320), (Sum.inr 1616, -4320), (Sum.inr 1617, -4320), (Sum.inr 1618, -4320), (Sum.inr 1623, -4320), (Sum.inr 1724, -4320), (Sum.inr 2383, -4320), (Sum.inr 2385, -4320), (Sum.inr 2388, -4320), (Sum.inr 2404, -4320), (Sum.inr 2449, -4320), (Sum.inr 2452, -4320), (Sum.inr 2462, -4320), (Sum.inr 2480, -4320), (Sum.inr 2482, -4320), (Sum.inr 2556, -4320), (Sum.inr 2561, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -4320), (Sum.inr 2739, -4320), (Sum.inr 2743, -4320), (Sum.inr 3352, -4320), (Sum.inr 3353, -4320), (Sum.inr 3354, -4320), (Sum.inr 3357, -4320), (Sum.inr 3432, -4320), (Sum.inr 3433, -4320), (Sum.inr 3436, -4320), (Sum.inr 3467, -4320), (Sum.inr 3468, -4320), (Sum.inr 3521, -4320), (Sum.inr 3522, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -4320), (Sum.inr 3548, -4320), (Sum.inr 3607, -4320), (Sum.inr 3622, -4320), (Sum.inr 3627, -4320), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 4047, -4320)]

def numericRow498 : Integer.Sparse Master := [(Sum.inl 0, -323), (Sum.inl 6, 5), (Sum.inl 2, -55), (Sum.inl 8, -80), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -5), (Sum.inr 980, 4320), (Sum.inr 982, 4320), (Sum.inr 985, 4320), (Sum.inr 1005, 4320), (Sum.inr 1041, 4320), (Sum.inr 2383, 4320), (Sum.inr 2385, 4320), (Sum.inr 2388, 4320), (Sum.inr 2404, 4320), (Sum.inr 2449, 4320), (Sum.inr 2452, 4320), (Sum.inr 2462, 4320), (Sum.inr 2480, 4320), (Sum.inr 2482, 4320), (Sum.inr 2556, 4320), (Sum.inr 2561, 4320), (Sum.inr 2721, 4320), (Sum.inr 2722, 4320), (Sum.inr 2723, 4320), (Sum.inr 2726, 4320), (Sum.inr 2739, 4320), (Sum.inr 2743, 4320), (Sum.inr 3958, 4320)]

def numericRow499 : Integer.Sparse Master := [(Sum.inl 0, 67), (Sum.inl 2, -85), (Sum.inl 3, -80), (Sum.inl 1, -100), (Sum.inr 2051, -2160), (Sum.inr 2054, -2160), (Sum.inr 2058, -2160), (Sum.inr 2191, -2160), (Sum.inr 2206, -2160), (Sum.inr 2216, -2160), (Sum.inr 2672, -2160), (Sum.inr 2694, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -6480), (Sum.inr 2743, -2160), (Sum.inr 3391, -2160), (Sum.inr 3493, -2160), (Sum.inr 3533, -4320), (Sum.inr 3544, -6480), (Sum.inr 3548, -2160), (Sum.inr 3627, -4320), (Sum.inr 3632, -2160), (Sum.inr 5220, 8640), (Sum.inr 5229, 8640), (Sum.inr 5233, 8640), (Sum.inr 5244, 8640), (Sum.inr 5251, 8640), (Sum.inr 5260, 8640), (Sum.inr 5266, 17280), (Sum.inr 5267, 8640)]

def numericRow500 : Integer.Sparse Master := [(Sum.inl 0, -394), (Sum.inl 2, 500), (Sum.inl 26, -160), (Sum.inl 1, 510), (Sum.inr 2191, 8640), (Sum.inr 2206, 8640), (Sum.inr 2216, 8640), (Sum.inr 2662, 8640), (Sum.inr 2672, 8640), (Sum.inr 2673, 8640), (Sum.inr 2678, 8640), (Sum.inr 2694, 8640), (Sum.inr 2698, 8640), (Sum.inr 2710, 8640), (Sum.inr 2722, 8640), (Sum.inr 2723, 17280), (Sum.inr 2724, 8640), (Sum.inr 2731, 8640), (Sum.inr 2732, 8640), (Sum.inr 2743, 8640), (Sum.inr 3039, 8640)]

def numericRow501 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 29), (Sum.inl 3, 16), (Sum.inl 1, 32), (Sum.inr 2722, 216), (Sum.inr 2723, 216), (Sum.inr 2731, 216), (Sum.inr 3029, 216), (Sum.inr 3038, 216), (Sum.inr 3039, 216), (Sum.inr 3044, 216), (Sum.inr 3064, 216), (Sum.inr 3068, 216), (Sum.inr 3086, 216), (Sum.inr 3092, 216)]

def numericRow502 : Integer.Sparse Master := [(Sum.inr 2051, 1), (Sum.inr 2054, 1), (Sum.inr 2058, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

def numericRow503 : Integer.Sparse Master := [(Sum.inl 0, 48), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 1236, -4320), (Sum.inr 2479, -4320), (Sum.inr 2482, -4320), (Sum.inr 2488, -4320), (Sum.inr 2553, -4320), (Sum.inr 2722, -4320), (Sum.inr 2726, -4320), (Sum.inr 2739, -4320), (Sum.inr 2765, -4320), (Sum.inr 3293, -4320), (Sum.inr 3459, -4320), (Sum.inr 3468, -4320), (Sum.inr 3478, -4320), (Sum.inr 3514, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3545, -4320), (Sum.inr 3582, -4320), (Sum.inr 3837, -8640), (Sum.inr 3850, -8640), (Sum.inr 3903, -4320), (Sum.inr 4589, 17280), (Sum.inr 4591, 17280), (Sum.inr 4592, 17280), (Sum.inr 4607, 17280), (Sum.inr 5129, 17280), (Sum.inr 5144, 17280), (Sum.inr 5147, 17280), (Sum.inr 5184, 17280), (Sum.inr 5188, 17280), (Sum.inr 5198, 17280), (Sum.inr 5260, 17280), (Sum.inr 5289, 17280)]

def numericRow504 : Integer.Sparse Master := [(Sum.inl 0, -196), (Sum.inl 2, -210), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 1, 170), (Sum.inr 1216, 2160), (Sum.inr 1217, 2160), (Sum.inr 1219, 2160), (Sum.inr 1241, 2160), (Sum.inr 2864, 2160), (Sum.inr 2865, 2160), (Sum.inr 2867, 2160), (Sum.inr 2885, 2160), (Sum.inr 2916, 2160), (Sum.inr 2928, 2160), (Sum.inr 3086, 2160), (Sum.inr 3097, 2160)]

def numericRow505 : Integer.Sparse Master := [(Sum.inl 0, -48), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 35), (Sum.inr 3288, 4320), (Sum.inr 3291, 4320), (Sum.inr 3293, 4320), (Sum.inr 3295, 4320), (Sum.inr 3296, 4320), (Sum.inr 3459, 4320), (Sum.inr 3468, 4320), (Sum.inr 3478, 4320), (Sum.inr 3514, 4320), (Sum.inr 3516, 4320), (Sum.inr 3524, 4320), (Sum.inr 3530, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3538, 4320), (Sum.inr 3540, 4320), (Sum.inr 3545, 4320), (Sum.inr 3557, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3582, 4320), (Sum.inr 3837, 4320), (Sum.inr 3850, 4320)]

def numericRow506 : Integer.Sparse Master := [(Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 3850, 1), (Sum.inr 3903, 1), (Sum.inr 4092, -1)]

def numericRow507 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1215, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 2722, 1), (Sum.inr 4092, -1)]

def numericRow508 : Integer.Sparse Master := [(Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 2722, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

def numericRow509 : Integer.Sparse Master := [(Sum.inr 2569, 1), (Sum.inr 2614, 1), (Sum.inr 2620, 1), (Sum.inr 2632, 1), (Sum.inr 2722, 1), (Sum.inr 3850, 1), (Sum.inr 4092, -1)]

def numericRow510 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 2614, 1), (Sum.inr 2722, 2), (Sum.inr 4092, -1)]

def numericRow511 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2722, 1), (Sum.inr 3837, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow512 : Integer.Sparse Master := [(Sum.inl 0, 300), (Sum.inl 6, -5), (Sum.inl 2, 70), (Sum.inl 7, 80), (Sum.inl 3, 320), (Sum.inl 12, 80), (Sum.inl 4, 240), (Sum.inl 1, 175), (Sum.inr 977, -4320), (Sum.inr 979, -4320), (Sum.inr 985, -4320), (Sum.inr 1000, -4320), (Sum.inr 1040, -4320), (Sum.inr 1597, -4320), (Sum.inr 1599, -4320), (Sum.inr 1605, -4320), (Sum.inr 1618, -4320), (Sum.inr 1707, -4320), (Sum.inr 1987, -4320), (Sum.inr 1996, -4320), (Sum.inr 2003, -4320), (Sum.inr 2006, -4320), (Sum.inr 2022, -4320), (Sum.inr 2052, -4320), (Sum.inr 2193, -4320), (Sum.inr 2203, -4320), (Sum.inr 2382, -4320), (Sum.inr 2388, -4320), (Sum.inr 2400, -4320), (Sum.inr 2452, -4320), (Sum.inr 2459, -4320), (Sum.inr 2479, -4320), (Sum.inr 2553, -4320), (Sum.inr 2561, -4320), (Sum.inr 2694, -4320), (Sum.inr 2705, -4320), (Sum.inr 2721, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2739, -4320), (Sum.inr 3340, -4320), (Sum.inr 3344, -4320), (Sum.inr 3354, -4320), (Sum.inr 3429, -4320), (Sum.inr 3433, -4320), (Sum.inr 3459, -4320), (Sum.inr 3493, -4320), (Sum.inr 3498, -4320), (Sum.inr 3514, -4320), (Sum.inr 3522, -4320), (Sum.inr 3532, -4320), (Sum.inr 3533, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3603, -4320), (Sum.inr 3622, -4320), (Sum.inr 3838, -4320), (Sum.inr 3843, -4320), (Sum.inr 3845, -8640), (Sum.inr 3902, -4320), (Sum.inr 3903, -4320)]

def numericRow513 : Integer.Sparse Master := [(Sum.inl 0, -40), (Sum.inl 6, 1), (Sum.inl 2, -15), (Sum.inl 7, -16), (Sum.inl 3, -48), (Sum.inl 4, -32), (Sum.inl 1, -12), (Sum.inr 977, 864), (Sum.inr 979, 864), (Sum.inr 985, 864), (Sum.inr 1000, 864), (Sum.inr 1040, 864), (Sum.inr 1987, 864), (Sum.inr 2003, 864), (Sum.inr 2022, 864), (Sum.inr 2193, 864), (Sum.inr 2382, 864), (Sum.inr 2388, 864), (Sum.inr 2400, 864), (Sum.inr 2452, 864), (Sum.inr 2459, 864), (Sum.inr 2479, 864), (Sum.inr 2553, 864), (Sum.inr 2561, 864), (Sum.inr 2694, 864), (Sum.inr 2705, 864), (Sum.inr 2721, 864), (Sum.inr 2722, 864), (Sum.inr 2723, 864), (Sum.inr 2739, 864), (Sum.inr 3838, 864), (Sum.inr 3845, 864), (Sum.inr 3902, 864)]

def numericRow514 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2019, -2160), (Sum.inr 2022, -2160), (Sum.inr 2028, -2160), (Sum.inr 2190, -2160), (Sum.inr 2203, -2160), (Sum.inr 2215, -2160), (Sum.inr 2672, -2160), (Sum.inr 2694, -2160), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 2765, -2160), (Sum.inr 3391, -2160), (Sum.inr 3493, -2160), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3582, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 5140, 8640), (Sum.inr 5161, 8640), (Sum.inr 5219, 8640), (Sum.inr 5232, 8640), (Sum.inr 5243, 8640), (Sum.inr 5249, 8640), (Sum.inr 5251, 8640), (Sum.inr 5260, 8640), (Sum.inr 5264, 8640), (Sum.inr 5266, 8640), (Sum.inr 5267, 8640)]

def numericRow515 : Integer.Sparse Master := [(Sum.inl 0, -23), (Sum.inl 2, 29), (Sum.inl 3, 16), (Sum.inl 1, 32), (Sum.inr 2190, 864), (Sum.inr 2203, 864), (Sum.inr 2215, 864), (Sum.inr 2661, 864), (Sum.inr 2670, 864), (Sum.inr 2672, 864), (Sum.inr 2677, 864), (Sum.inr 2694, 864), (Sum.inr 2697, 864), (Sum.inr 2708, 864), (Sum.inr 2719, 864), (Sum.inr 2722, 1728), (Sum.inr 2723, 864), (Sum.inr 2729, 864), (Sum.inr 2731, 864), (Sum.inr 2740, 864), (Sum.inr 2765, 864), (Sum.inr 3038, 864), (Sum.inr 3064, 864), (Sum.inr 3086, 864)]

def numericRow516 : Integer.Sparse Master := [(Sum.inl 0, -220), (Sum.inl 2, 270), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 1, 290), (Sum.inr 2710, 2160), (Sum.inr 2723, 2160), (Sum.inr 2724, 2160), (Sum.inr 2732, 2160), (Sum.inr 2942, 2160), (Sum.inr 2964, 2160), (Sum.inr 3030, 2160), (Sum.inr 3039, 2160), (Sum.inr 3040, 2160), (Sum.inr 3045, 2160), (Sum.inr 3066, 2160), (Sum.inr 3069, 2160)]

def numericRow517 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 3533, 1), (Sum.inr 4084, -1)]

def numericRow518 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, -1), (Sum.inr 3309, -72), (Sum.inr 3310, -24), (Sum.inr 3312, -24), (Sum.inr 3607, -144), (Sum.inr 3615, -72), (Sum.inr 3616, -72), (Sum.inr 3627, -72), (Sum.inr 3634, -24)]

def numericRow519 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 1, 5), (Sum.inr 3308, -90), (Sum.inr 3310, -30), (Sum.inr 3311, -30), (Sum.inr 3603, -180), (Sum.inr 3608, -90), (Sum.inr 3614, -90), (Sum.inr 3623, -90), (Sum.inr 3633, -30)]

def numericRow520 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1297, -144), (Sum.inr 2109, -432), (Sum.inr 2261, -432), (Sum.inr 2289, -144), (Sum.inr 2740, -864), (Sum.inr 2765, -432), (Sum.inr 3582, -432), (Sum.inr 3633, -144), (Sum.inr 4617, 1728), (Sum.inr 4626, 576), (Sum.inr 5161, 3456), (Sum.inr 5175, 1728), (Sum.inr 5295, 1728), (Sum.inr 5311, 576)]

def numericRow521 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 2, 40), (Sum.inl 26, 160), (Sum.inl 1, 30), (Sum.inr 1306, 1440), (Sum.inr 1310, 480), (Sum.inr 2769, 1440), (Sum.inr 2789, 480), (Sum.inr 2964, 2880), (Sum.inr 2967, 1440)]

def numericRow522 : Integer.Sparse Master := [(Sum.inl 0, -1), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, -2), (Sum.inr 2261, 432), (Sum.inr 2289, 144), (Sum.inr 2719, 864), (Sum.inr 2737, 432), (Sum.inr 2740, 432), (Sum.inr 2761, 432), (Sum.inr 2765, 432), (Sum.inr 2780, 144), (Sum.inr 2789, 144), (Sum.inr 3098, 432)]

def numericRow523 : Integer.Sparse Master := [(Sum.inl 0, 12), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 80), (Sum.inl 1, -5), (Sum.inr 1074, -2160), (Sum.inr 1077, -720), (Sum.inr 1094, -720), (Sum.inr 1650, -2160), (Sum.inr 1741, -720), (Sum.inr 2504, -4320), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2782, -2160), (Sum.inr 3583, -2160), (Sum.inr 3633, -720)]

def numericRow524 : Integer.Sparse Master := [(Sum.inl 0, 15), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, -80), (Sum.inl 1, 50), (Sum.inr 1246, -2160), (Sum.inr 2512, -4320), (Sum.inr 2519, -2160), (Sum.inr 2561, -4320), (Sum.inr 2739, -4320), (Sum.inr 2782, -2160), (Sum.inr 3301, -2160), (Sum.inr 3471, -4320), (Sum.inr 3486, -2160), (Sum.inr 3522, -4320), (Sum.inr 3534, -4320), (Sum.inr 3583, -2160), (Sum.inr 3845, -8640), (Sum.inr 3907, -2160), (Sum.inr 4603, 17280), (Sum.inr 4609, 8640), (Sum.inr 4620, 8640), (Sum.inr 5139, 17280), (Sum.inr 5164, 17280), (Sum.inr 5266, 17280), (Sum.inr 5268, 8640), (Sum.inr 5300, 8640)]

def numericRow525 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 1262, 1080), (Sum.inr 1264, 540), (Sum.inr 1295, 540), (Sum.inr 2618, 1080), (Sum.inr 2734, 540), (Sum.inr 2955, 1080), (Sum.inr 3039, 1080), (Sum.inr 3055, 540)]

def numericRow526 : Integer.Sparse Master := [(Sum.inl 0, -15), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 1, -50), (Sum.inr 3294, 4320), (Sum.inr 3301, 2160), (Sum.inr 3302, 2160), (Sum.inr 3306, 2160), (Sum.inr 3471, 4320), (Sum.inr 3486, 2160), (Sum.inr 3522, 4320), (Sum.inr 3523, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3549, 2160), (Sum.inr 3565, 4320), (Sum.inr 3583, 2160), (Sum.inr 3584, 2160), (Sum.inr 3845, 4320)]

def numericRow527 : Integer.Sparse Master := [(Sum.inr 2743, 1), (Sum.inr 3845, 2), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow528 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 2591, 1), (Sum.inr 2743, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

def numericRow529 : Integer.Sparse Master := [(Sum.inr 2512, 2), (Sum.inr 2519, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def numericRow530 : Integer.Sparse Master := [(Sum.inr 1246, 1), (Sum.inr 2561, 2), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def numericRow531 : Integer.Sparse Master := [(Sum.inl 0, 137), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 4, -160), (Sum.inl 1, 290), (Sum.inr 1005, -4320), (Sum.inr 1009, -2160), (Sum.inr 1012, -2160), (Sum.inr 1083, -2160), (Sum.inr 1623, -4320), (Sum.inr 1627, -2160), (Sum.inr 1630, -2160), (Sum.inr 1728, -2160), (Sum.inr 2385, -4320), (Sum.inr 2399, -4320), (Sum.inr 2404, -4320), (Sum.inr 2407, -2160), (Sum.inr 2410, -4320), (Sum.inr 2462, -4320), (Sum.inr 2467, -4320), (Sum.inr 2512, -4320), (Sum.inr 2723, -4320), (Sum.inr 2726, -2160), (Sum.inr 2739, -4320), (Sum.inr 2740, -4320), (Sum.inr 3353, -4320), (Sum.inr 3357, -4320), (Sum.inr 3360, -2160), (Sum.inr 3436, -4320), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3544, -4320), (Sum.inr 3545, -2160), (Sum.inr 3623, -2160), (Sum.inr 3627, -2160), (Sum.inr 3958, -4320), (Sum.inr 3961, -4320), (Sum.inr 3963, -4320)]

def numericRow532 : Integer.Sparse Master := [(Sum.inl 0, -18), (Sum.inl 2, 5), (Sum.inl 3, 16), (Sum.inl 4, 16), (Sum.inl 1, -37), (Sum.inr 1005, 864), (Sum.inr 1009, 432), (Sum.inr 1012, 432), (Sum.inr 1083, 432), (Sum.inr 2385, 864), (Sum.inr 2404, 864), (Sum.inr 2407, 432), (Sum.inr 2410, 432), (Sum.inr 2462, 864), (Sum.inr 2467, 864), (Sum.inr 2512, 864), (Sum.inr 2723, 864), (Sum.inr 2726, 432), (Sum.inr 2739, 864), (Sum.inr 2740, 432), (Sum.inr 3958, 864), (Sum.inr 3963, 432)]

def numericRow533 : Integer.Sparse Master := [(Sum.inl 0, 13), (Sum.inl 2, -15), (Sum.inl 3, 80), (Sum.inr 2054, -1440), (Sum.inr 2062, -720), (Sum.inr 2206, -1440), (Sum.inr 2230, -720), (Sum.inr 2686, -720), (Sum.inr 2705, -1440), (Sum.inr 2723, -1440), (Sum.inr 2743, -1440), (Sum.inr 2765, -720), (Sum.inr 3397, -720), (Sum.inr 3498, -1440), (Sum.inr 3544, -1440), (Sum.inr 3548, -1440), (Sum.inr 3582, -720), (Sum.inr 3627, -720), (Sum.inr 3633, -720), (Sum.inr 5205, 5760), (Sum.inr 5206, 2880), (Sum.inr 5229, 5760), (Sum.inr 5260, 5760), (Sum.inr 5276, 2880), (Sum.inr 5282, 5760), (Sum.inr 5300, 2880)]

def numericRow534 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, 120), (Sum.inl 3, -320), (Sum.inl 26, 160), (Sum.inl 1, 50), (Sum.inr 2206, 8640), (Sum.inr 2230, 4320), (Sum.inr 2673, 8640), (Sum.inr 2686, 4320), (Sum.inr 2687, 4320), (Sum.inr 2705, 8640), (Sum.inr 2706, 8640), (Sum.inr 2723, 8640), (Sum.inr 2724, 8640), (Sum.inr 2743, 8640), (Sum.inr 2744, 4320), (Sum.inr 3055, 4320), (Sum.inr 3078, 8640)]

def numericRow535 : Integer.Sparse Master := [(Sum.inr 2054, 2), (Sum.inr 2062, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

def numericRow536 : Integer.Sparse Master := [(Sum.inr 1236, -2), (Sum.inr 1242, -1), (Sum.inr 1246, -1), (Sum.inr 1294, -1), (Sum.inr 2482, -2), (Sum.inr 2553, -2), (Sum.inr 2561, -2), (Sum.inr 2590, -2), (Sum.inr 2722, -2), (Sum.inr 2726, -1), (Sum.inr 2739, -2), (Sum.inr 2743, -1), (Sum.inr 2765, -1), (Sum.inr 2782, -1), (Sum.inr 3293, -2), (Sum.inr 3300, -1), (Sum.inr 3301, -1), (Sum.inr 3305, -1), (Sum.inr 3468, -2), (Sum.inr 3514, -2), (Sum.inr 3522, -2), (Sum.inr 3533, -2), (Sum.inr 3534, -2), (Sum.inr 3545, -1), (Sum.inr 3548, -1), (Sum.inr 3564, -2), (Sum.inr 3582, -1), (Sum.inr 3583, -1), (Sum.inr 4092, 4)]

def numericRow537 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 2509, -4320), (Sum.inr 2522, -2160), (Sum.inr 2672, -4320), (Sum.inr 2685, -2160), (Sum.inr 2686, -2160), (Sum.inr 2694, -4320), (Sum.inr 2704, -4320), (Sum.inr 2705, -4320), (Sum.inr 2722, -4320), (Sum.inr 2723, -4320), (Sum.inr 2740, -4320), (Sum.inr 2743, -2160), (Sum.inr 3054, -2160), (Sum.inr 3077, -4320), (Sum.inr 3391, -4320), (Sum.inr 3397, -2160), (Sum.inr 3493, -4320), (Sum.inr 3498, -4320), (Sum.inr 3533, -4320), (Sum.inr 3544, -4320), (Sum.inr 3548, -2160), (Sum.inr 3625, -4320), (Sum.inr 3626, -2160), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4084, 8640)]

def numericRow538 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1239, -2160), (Sum.inr 2022, -4320), (Sum.inr 2203, -4320), (Sum.inr 2226, -2160), (Sum.inr 2509, -4320), (Sum.inr 2522, -2160), (Sum.inr 2685, -2160), (Sum.inr 2704, -4320), (Sum.inr 2722, -4320), (Sum.inr 2740, -8640), (Sum.inr 2783, -4320), (Sum.inr 3533, -4320), (Sum.inr 3632, -2160), (Sum.inr 4600, 17280), (Sum.inr 4611, 8640), (Sum.inr 4617, 8640), (Sum.inr 5140, 17280), (Sum.inr 5161, 17280), (Sum.inr 5270, 17280), (Sum.inr 5276, 8640), (Sum.inr 5295, 8640)]

def numericRow539 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, 140), (Sum.inl 26, -160), (Sum.inl 1, 150), (Sum.inr 1270, 2160), (Sum.inr 1273, 1080), (Sum.inr 1306, 1080), (Sum.inr 2754, 2160), (Sum.inr 2769, 1080), (Sum.inr 2777, 1080), (Sum.inr 2942, 2160), (Sum.inr 2964, 2160)]

def numericRow540 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 25), (Sum.inl 3, 80), (Sum.inl 1, 40), (Sum.inr 2203, 4320), (Sum.inr 2226, 2160), (Sum.inr 2670, 4320), (Sum.inr 2683, 2160), (Sum.inr 2685, 2160), (Sum.inr 2702, 4320), (Sum.inr 2704, 4320), (Sum.inr 2719, 4320), (Sum.inr 2722, 4320), (Sum.inr 2737, 2160), (Sum.inr 2740, 4320), (Sum.inr 2783, 2160), (Sum.inr 3052, 2160), (Sum.inr 3075, 4320), (Sum.inr 3098, 2160)]

def numericRow541 : Integer.Sparse Master := [(Sum.inl 0, 42), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, 95), (Sum.inr 999, -4320), (Sum.inr 1002, -2160), (Sum.inr 1012, -2160), (Sum.inr 1080, -2160), (Sum.inr 1602, -4320), (Sum.inr 1627, -2160), (Sum.inr 1710, -2160), (Sum.inr 2399, -4320), (Sum.inr 2410, -2160), (Sum.inr 2458, -4320), (Sum.inr 2467, -4320), (Sum.inr 2509, -4320), (Sum.inr 2704, -4320), (Sum.inr 2739, -4320), (Sum.inr 2740, -2160), (Sum.inr 2743, -2160), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3623, -2160)]

def numericRow542 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1087, -2160), (Sum.inr 1739, -2160), (Sum.inr 2058, -4320), (Sum.inr 2216, -4320), (Sum.inr 2245, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -4320), (Sum.inr 2278, -4320), (Sum.inr 3054, -2160), (Sum.inr 3626, -2160), (Sum.inr 3632, -2160), (Sum.inr 4475, 17280), (Sum.inr 4478, 8640), (Sum.inr 4480, 8640), (Sum.inr 4816, 17280), (Sum.inr 4819, 17280), (Sum.inr 4821, 17280), (Sum.inr 4844, 8640), (Sum.inr 4880, 17280), (Sum.inr 4884, 8640), (Sum.inr 4891, 17280), (Sum.inr 4892, 8640), (Sum.inr 5267, 17280), (Sum.inr 5276, 8640)]

def numericRow543 : Integer.Sparse Master := [(Sum.inl 0, -30), (Sum.inl 2, 35), (Sum.inl 3, 160), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, 5), (Sum.inr 1715, 4320), (Sum.inr 1739, 2160), (Sum.inr 1740, 2160), (Sum.inr 1746, 2160), (Sum.inr 2196, 4320), (Sum.inr 2216, 4320), (Sum.inr 2217, 4320), (Sum.inr 2221, 4320), (Sum.inr 2222, 2160), (Sum.inr 2245, 4320), (Sum.inr 2253, 4320), (Sum.inr 2254, 4320), (Sum.inr 2266, 2160), (Sum.inr 2278, 2160), (Sum.inr 2280, 2160), (Sum.inr 2284, 2160), (Sum.inr 2732, 4320), (Sum.inr 2777, 2160)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow544 : Integer.Sparse Master := [(Sum.inr 1087, 1), (Sum.inr 2058, 2), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

def numericRow545 : Integer.Sparse Master := [(Sum.inl 0, 27), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 12, 160), (Sum.inl 1, 230), (Sum.inr 827, -4320), (Sum.inr 828, -2160), (Sum.inr 830, -2160), (Sum.inr 857, -2160), (Sum.inr 1925, -4320), (Sum.inr 1926, -4320), (Sum.inr 1928, -4320), (Sum.inr 1948, -4320), (Sum.inr 2110, -4320), (Sum.inr 2112, -2160), (Sum.inr 2115, -2160), (Sum.inr 2275, -4320), (Sum.inr 2276, -2160), (Sum.inr 2279, -4320), (Sum.inr 2281, -2160), (Sum.inr 2287, -2160), (Sum.inr 2294, -2160), (Sum.inr 3814, -4320), (Sum.inr 3907, -2160)]

def numericRow546 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -20), (Sum.inl 3, 80), (Sum.inl 1, -5), (Sum.inr 1083, -1080), (Sum.inr 1728, -1080), (Sum.inr 2054, -2160), (Sum.inr 2206, -2160), (Sum.inr 2245, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -2160), (Sum.inr 2281, -1080), (Sum.inr 2294, -1080), (Sum.inr 3632, -1080), (Sum.inr 3633, -1080), (Sum.inr 4474, 8640), (Sum.inr 4476, 4320), (Sum.inr 4480, 4320), (Sum.inr 4815, 8640), (Sum.inr 4817, 8640), (Sum.inr 4821, 8640), (Sum.inr 4879, 8640), (Sum.inr 4881, 4320), (Sum.inr 4884, 4320), (Sum.inr 5260, 8640), (Sum.inr 5295, 4320)]

def numericRow547 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 50), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, 35), (Sum.inr 1370, 1440), (Sum.inr 1372, 720), (Sum.inr 1375, 720), (Sum.inr 2497, 1440), (Sum.inr 2520, 720), (Sum.inr 3086, 1440), (Sum.inr 3098, 720), (Sum.inr 3158, 1440), (Sum.inr 3161, 720), (Sum.inr 3197, 1440), (Sum.inr 3198, 1440)]

def numericRow548 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, 20), (Sum.inl 3, -80), (Sum.inl 1, 5), (Sum.inr 1709, 2160), (Sum.inr 1728, 1080), (Sum.inr 1729, 1080), (Sum.inr 1740, 1080), (Sum.inr 2192, 2160), (Sum.inr 2206, 2160), (Sum.inr 2207, 2160), (Sum.inr 2217, 2160), (Sum.inr 2245, 2160), (Sum.inr 2246, 2160), (Sum.inr 2266, 2160), (Sum.inr 2267, 1080), (Sum.inr 2279, 1080), (Sum.inr 2280, 1080), (Sum.inr 2294, 1080), (Sum.inr 2724, 2160), (Sum.inr 2769, 1080)]

def numericRow549 : Integer.Sparse Master := [(Sum.inr 1057, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

def numericRow550 : Integer.Sparse Master := [(Sum.inr 1083, 1), (Sum.inr 2054, 2), (Sum.inr 2278, 1), (Sum.inr 4084, -1)]

def numericRow551 : Integer.Sparse Master := [(Sum.inl 0, 73), (Sum.inl 2, 10), (Sum.inl 3, -160), (Sum.inl 12, -240), (Sum.inl 4, -80), (Sum.inl 1, 145), (Sum.inr 811, -4320), (Sum.inr 813, -2160), (Sum.inr 815, -2160), (Sum.inr 824, -4320), (Sum.inr 826, -2160), (Sum.inr 831, -2160), (Sum.inr 853, -2160), (Sum.inr 858, -2160), (Sum.inr 1913, -4320), (Sum.inr 1915, -4320), (Sum.inr 1917, -4320), (Sum.inr 1922, -4320), (Sum.inr 1924, -4320), (Sum.inr 1929, -4320), (Sum.inr 1946, -4320), (Sum.inr 1949, -4320), (Sum.inr 2058, -4320), (Sum.inr 2062, -2160), (Sum.inr 2065, -2160), (Sum.inr 2107, -4320), (Sum.inr 2109, -2160), (Sum.inr 2116, -2160), (Sum.inr 2216, -4320), (Sum.inr 2218, -2160), (Sum.inr 2230, -2160), (Sum.inr 2245, -4320), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2261, -2160), (Sum.inr 2266, -2160), (Sum.inr 2277, -4320), (Sum.inr 2278, -2160), (Sum.inr 2288, -2160), (Sum.inr 2290, -2160), (Sum.inr 3809, -4320), (Sum.inr 3813, -4320), (Sum.inr 3907, -2160), (Sum.inr 3913, -2160)]

def numericRow552 : Integer.Sparse Master := [(Sum.inl 0, -38), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 80), (Sum.inl 4, 80), (Sum.inl 1, -35), (Sum.inr 824, 4320), (Sum.inr 826, 2160), (Sum.inr 831, 2160), (Sum.inr 853, 2160), (Sum.inr 1922, 4320), (Sum.inr 1924, 4320), (Sum.inr 1929, 4320), (Sum.inr 1946, 4320), (Sum.inr 2107, 4320), (Sum.inr 2109, 2160), (Sum.inr 2116, 2160), (Sum.inr 2216, 4320), (Sum.inr 2218, 2160), (Sum.inr 2230, 2160), (Sum.inr 2277, 4320), (Sum.inr 2278, 2160), (Sum.inr 2290, 2160), (Sum.inr 3813, 4320), (Sum.inr 3907, 2160)]

def numericRow553 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1049, -360), (Sum.inr 1087, -360), (Sum.inr 1738, -360), (Sum.inr 1739, -360), (Sum.inr 2028, -720), (Sum.inr 2058, -720), (Sum.inr 2115, -360), (Sum.inr 2215, -720), (Sum.inr 2216, -720), (Sum.inr 2244, -720), (Sum.inr 2262, -720), (Sum.inr 2276, -360), (Sum.inr 2279, -720), (Sum.inr 3054, -360), (Sum.inr 3626, -360), (Sum.inr 3627, -360), (Sum.inr 4459, 2880), (Sum.inr 4464, 1440), (Sum.inr 4803, 2880), (Sum.inr 4808, 2880), (Sum.inr 4867, 2880), (Sum.inr 4872, 1440), (Sum.inr 4891, 2880), (Sum.inr 4892, 1440), (Sum.inr 5266, 2880), (Sum.inr 5300, 1440)]

def numericRow554 : Integer.Sparse Master := [(Sum.inl 0, -35), (Sum.inl 2, 40), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 12, 80), (Sum.inl 1, -5), (Sum.inr 1714, 4320), (Sum.inr 1738, 2160), (Sum.inr 1739, 2160), (Sum.inr 1745, 2160), (Sum.inr 2195, 4320), (Sum.inr 2215, 4320), (Sum.inr 2216, 4320), (Sum.inr 2220, 4320), (Sum.inr 2244, 4320), (Sum.inr 2251, 4320), (Sum.inr 2253, 4320), (Sum.inr 2276, 2160), (Sum.inr 2279, 2160), (Sum.inr 2282, 2160), (Sum.inr 2284, 2160), (Sum.inr 2731, 4320), (Sum.inr 2774, 2160)]

def numericRow555 : Integer.Sparse Master := [(Sum.inl 0, -57), (Sum.inl 2, 50), (Sum.inl 3, -80), (Sum.inl 13, -80), (Sum.inl 1, 35), (Sum.inr 1406, 1440), (Sum.inr 1408, 720), (Sum.inr 2092, 1440), (Sum.inr 2113, 720), (Sum.inr 2255, 720), (Sum.inr 3039, 1440), (Sum.inr 3054, 720), (Sum.inr 3055, 720), (Sum.inr 3180, 1440), (Sum.inr 3202, 1440), (Sum.inr 3222, 1440)]

def numericRow556 : Integer.Sparse Master := [(Sum.inr 1042, 2), (Sum.inr 1047, 1), (Sum.inr 1049, 1), (Sum.inr 1087, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

def numericRow557 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 1044, -8640), (Sum.inr 1737, -8640), (Sum.inr 2023, -8640), (Sum.inr 2110, -8640), (Sum.inr 2214, -8640), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -8640), (Sum.inr 2262, -4320), (Sum.inr 2275, -8640), (Sum.inr 2277, -8640), (Sum.inr 3053, -4320), (Sum.inr 3619, -4320), (Sum.inr 3622, -4320), (Sum.inr 4439, 17280), (Sum.inr 4442, 17280), (Sum.inr 4444, 17280), (Sum.inr 4793, 17280), (Sum.inr 4795, 17280), (Sum.inr 4808, 34560), (Sum.inr 4852, 34560), (Sum.inr 4856, 34560), (Sum.inr 4885, 17280), (Sum.inr 4886, 17280), (Sum.inr 5265, 17280), (Sum.inr 5299, 34560)]

def numericRow558 : Integer.Sparse Master := [(Sum.inl 0, -29), (Sum.inl 2, -35), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -120), (Sum.inl 1, -50), (Sum.inr 1713, 2160), (Sum.inr 1736, 2160), (Sum.inr 1737, 4320), (Sum.inr 1744, 2160), (Sum.inr 2213, 2160), (Sum.inr 2214, 4320), (Sum.inr 2219, 2160), (Sum.inr 2220, 4320), (Sum.inr 2243, 2160), (Sum.inr 2250, 4320), (Sum.inr 2252, 2160), (Sum.inr 2262, 2160), (Sum.inr 2274, 4320), (Sum.inr 2275, 4320), (Sum.inr 2277, 4320), (Sum.inr 2283, 2160), (Sum.inr 2730, 2160), (Sum.inr 2773, 4320)]

def numericRow559 : Integer.Sparse Master := [(Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 2), (Sum.inr 3619, 1), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow560 : Integer.Sparse Master := [(Sum.inr 1044, 1), (Sum.inr 2023, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 2), (Sum.inr 4083, -1)]

def numericRow561 : Integer.Sparse Master := [(Sum.inr 2089, 1), (Sum.inr 2092, 1), (Sum.inr 2094, 1), (Sum.inr 2110, 1), (Sum.inr 2245, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow562 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 2012, 1), (Sum.inr 2023, 2), (Sum.inr 2245, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def numericRow563 : Integer.Sparse Master := [(Sum.inr 1026, 1), (Sum.inr 2012, 1), (Sum.inr 2094, 2), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

def numericRow564 : Integer.Sparse Master := [(Sum.inl 0, 93), (Sum.inl 2, 15), (Sum.inl 3, 240), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -90), (Sum.inr 786, -2160), (Sum.inr 787, -2160), (Sum.inr 789, -2160), (Sum.inr 811, -4320), (Sum.inr 822, -2160), (Sum.inr 823, -2160), (Sum.inr 824, -4320), (Sum.inr 847, -2160), (Sum.inr 1898, -2160), (Sum.inr 1900, -2160), (Sum.inr 1913, -4320), (Sum.inr 1921, -2160), (Sum.inr 1922, -4320), (Sum.inr 1940, -2160), (Sum.inr 2023, -4320), (Sum.inr 2025, -4320), (Sum.inr 2028, -4320), (Sum.inr 2058, -4320), (Sum.inr 2105, -2160), (Sum.inr 2106, -2160), (Sum.inr 2107, -4320), (Sum.inr 2214, -4320), (Sum.inr 2215, -4320), (Sum.inr 2216, -4320), (Sum.inr 2224, -4320), (Sum.inr 2241, -2160), (Sum.inr 2242, -2160), (Sum.inr 2245, -2160), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -2160), (Sum.inr 2278, -4320), (Sum.inr 2290, -2160), (Sum.inr 3801, -2160), (Sum.inr 3812, -2160), (Sum.inr 3906, -4320), (Sum.inr 3910, -2160)]

def numericRow565 : Integer.Sparse Master := [(Sum.inl 0, -28), (Sum.inl 2, -10), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 1, 50), (Sum.inr 786, 1080), (Sum.inr 787, 1080), (Sum.inr 789, 1080), (Sum.inr 811, 2160), (Sum.inr 1898, 1080), (Sum.inr 1900, 1080), (Sum.inr 1913, 2160), (Sum.inr 2023, 2160), (Sum.inr 2025, 2160), (Sum.inr 2028, 2160), (Sum.inr 2058, 2160), (Sum.inr 2241, 1080), (Sum.inr 2242, 1080), (Sum.inr 2245, 1080), (Sum.inr 2247, 1080), (Sum.inr 2260, 2160), (Sum.inr 2266, 2160), (Sum.inr 3801, 1080), (Sum.inr 3910, 1080)]

def numericRow566 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 1, -40), (Sum.inr 1079, -1080), (Sum.inr 1708, -1080), (Sum.inr 2051, -1080), (Sum.inr 2191, -1080), (Sum.inr 2244, -1080), (Sum.inr 2245, -2160), (Sum.inr 2262, -1080), (Sum.inr 2266, -2160), (Sum.inr 2277, -2160), (Sum.inr 2278, -2160), (Sum.inr 2279, -4320), (Sum.inr 3077, -1080), (Sum.inr 3625, -1080), (Sum.inr 3632, -2160), (Sum.inr 4473, 4320), (Sum.inr 4474, 4320), (Sum.inr 4475, 8640), (Sum.inr 4815, 4320), (Sum.inr 4816, 8640), (Sum.inr 4878, 4320), (Sum.inr 4879, 4320), (Sum.inr 4880, 8640), (Sum.inr 4885, 4320), (Sum.inr 4891, 8640), (Sum.inr 5251, 4320), (Sum.inr 5270, 4320)]

def numericRow567 : Integer.Sparse Master := [(Sum.inl 0, -94), (Sum.inl 2, 125), (Sum.inl 3, 160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 215), (Sum.inr 1699, 4320), (Sum.inr 1708, 4320), (Sum.inr 1709, 4320), (Sum.inr 1715, 8640), (Sum.inr 2191, 4320), (Sum.inr 2192, 4320), (Sum.inr 2196, 8640), (Sum.inr 2233, 4320), (Sum.inr 2234, 4320), (Sum.inr 2244, 4320), (Sum.inr 2245, 8640), (Sum.inr 2246, 4320), (Sum.inr 2253, 8640), (Sum.inr 2254, 8640), (Sum.inr 2266, 8640), (Sum.inr 2279, 8640), (Sum.inr 2710, 4320), (Sum.inr 2754, 4320)]

def numericRow568 : Integer.Sparse Master := [(Sum.inl 0, -118), (Sum.inl 2, 185), (Sum.inl 3, 160), (Sum.inl 13, 240), (Sum.inl 12, 80), (Sum.inl 1, 155), (Sum.inr 1366, 1440), (Sum.inr 1367, 2880), (Sum.inr 1370, 1440), (Sum.inr 3064, 1440), (Sum.inr 3075, 1440), (Sum.inr 3077, 1440), (Sum.inr 3155, 1440), (Sum.inr 3156, 2880), (Sum.inr 3158, 1440), (Sum.inr 3196, 2880), (Sum.inr 3197, 1440), (Sum.inr 3221, 1440), (Sum.inr 3222, 2880)]

def numericRow569 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 2), (Sum.inr 1079, 1), (Sum.inr 2277, 1), (Sum.inr 4084, -1)]

def numericRow570 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 1041, -1728), (Sum.inr 1724, -1728), (Sum.inr 2020, -1728), (Sum.inr 2107, -1728), (Sum.inr 2202, -1728), (Sum.inr 2243, -1728), (Sum.inr 2244, -864), (Sum.inr 2245, -864), (Sum.inr 2247, -864), (Sum.inr 2260, -1728), (Sum.inr 2262, -864), (Sum.inr 2277, -864), (Sum.inr 2290, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 4440, 3456), (Sum.inr 4444, 3456), (Sum.inr 4792, 3456), (Sum.inr 4795, 3456), (Sum.inr 4851, 6912), (Sum.inr 4853, 6912), (Sum.inr 4856, 6912), (Sum.inr 5289, 6912)]

def numericRow571 : Integer.Sparse Master := [(Sum.inl 0, -99), (Sum.inl 2, -140), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 1, -185), (Sum.inr 1388, 1080), (Sum.inr 1391, 1080), (Sum.inr 2471, 1080), (Sum.inr 2486, 2160), (Sum.inr 3097, 2160), (Sum.inr 3172, 2160), (Sum.inr 3174, 2160), (Sum.inr 3199, 1080)]

def numericRow572 : Integer.Sparse Master := [(Sum.inl 0, -17), (Sum.inl 2, -13), (Sum.inl 3, 16), (Sum.inl 1, -40), (Sum.inr 1723, 864), (Sum.inr 1724, 1728), (Sum.inr 1736, 864), (Sum.inr 2201, 864), (Sum.inr 2202, 1728), (Sum.inr 2213, 864), (Sum.inr 2240, 1728), (Sum.inr 2243, 864), (Sum.inr 2259, 1728), (Sum.inr 2260, 1728), (Sum.inr 2262, 864), (Sum.inr 2274, 1728), (Sum.inr 2277, 864), (Sum.inr 2290, 864), (Sum.inr 2763, 1728)]

def numericRow573 : Integer.Sparse Master := [(Sum.inr 2244, 1), (Sum.inr 3572, 2), (Sum.inr 3622, 1), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def numericRow574 : Integer.Sparse Master := [(Sum.inr 1022, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 2), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

def numericRow575 : Integer.Sparse Master := [(Sum.inr 1041, 1), (Sum.inr 2020, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow576 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2244, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def numericRow577 : Integer.Sparse Master := [(Sum.inr 2088, 2), (Sum.inr 2243, 1), (Sum.inr 2244, 2), (Sum.inr 4083, -1)]

def numericRow578 : Integer.Sparse Master := [(Sum.inl 0, 269), (Sum.inl 2, 45), (Sum.inl 3, 240), (Sum.inl 12, 240), (Sum.inl 4, 160), (Sum.inl 1, -180), (Sum.inr 783, -4320), (Sum.inr 785, -4320), (Sum.inr 790, -4320), (Sum.inr 803, -4320), (Sum.inr 804, -4320), (Sum.inr 807, -17280), (Sum.inr 848, -4320), (Sum.inr 1897, -4320), (Sum.inr 1901, -4320), (Sum.inr 1907, -4320), (Sum.inr 1909, -17280), (Sum.inr 1941, -4320), (Sum.inr 2020, -8640), (Sum.inr 2022, -8640), (Sum.inr 2029, -8640), (Sum.inr 2051, -4320), (Sum.inr 2052, -4320), (Sum.inr 2054, -17280), (Sum.inr 2191, -4320), (Sum.inr 2193, -4320), (Sum.inr 2202, -8640), (Sum.inr 2203, -8640), (Sum.inr 2206, -17280), (Sum.inr 2225, -8640), (Sum.inr 2243, -8640), (Sum.inr 2244, -12960), (Sum.inr 2262, -12960), (Sum.inr 3800, -4320), (Sum.inr 3805, -4320), (Sum.inr 3902, -4320), (Sum.inr 3903, -8640)]

def numericRow579 : Integer.Sparse Master := [(Sum.inl 0, -83), (Sum.inl 2, -25), (Sum.inl 3, -80), (Sum.inl 12, -40), (Sum.inl 4, -80), (Sum.inl 1, 110), (Sum.inr 783, 2160), (Sum.inr 785, 2160), (Sum.inr 790, 2160), (Sum.inr 807, 4320), (Sum.inr 1897, 2160), (Sum.inr 1901, 2160), (Sum.inr 1909, 4320), (Sum.inr 2020, 4320), (Sum.inr 2022, 4320), (Sum.inr 2029, 4320), (Sum.inr 2054, 4320), (Sum.inr 2191, 2160), (Sum.inr 2193, 2160), (Sum.inr 2206, 4320), (Sum.inr 2243, 2160), (Sum.inr 2244, 2160), (Sum.inr 2262, 4320), (Sum.inr 3800, 2160), (Sum.inr 3902, 2160)]

def numericRow580 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1040, -180), (Sum.inr 1079, -180), (Sum.inr 1707, -180), (Sum.inr 1708, -180), (Sum.inr 2019, -180), (Sum.inr 2051, -180), (Sum.inr 2106, -180), (Sum.inr 2190, -180), (Sum.inr 2191, -180), (Sum.inr 2242, -180), (Sum.inr 2244, -360), (Sum.inr 2245, -180), (Sum.inr 2262, -360), (Sum.inr 2266, -360), (Sum.inr 2277, -180), (Sum.inr 2278, -360), (Sum.inr 3077, -180), (Sum.inr 3625, -180), (Sum.inr 3627, -360), (Sum.inr 4459, 1440), (Sum.inr 4803, 1440), (Sum.inr 4863, 720), (Sum.inr 4867, 1440), (Sum.inr 4885, 720), (Sum.inr 4891, 1440), (Sum.inr 5282, 720)]

def numericRow581 : Integer.Sparse Master := [(Sum.inl 0, -114), (Sum.inl 2, 145), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -80), (Sum.inl 1, 175), (Sum.inr 1707, 4320), (Sum.inr 1708, 4320), (Sum.inr 1714, 8640), (Sum.inr 2190, 4320), (Sum.inr 2191, 4320), (Sum.inr 2195, 8640), (Sum.inr 2232, 4320), (Sum.inr 2233, 4320), (Sum.inr 2242, 4320), (Sum.inr 2244, 8640), (Sum.inr 2245, 4320), (Sum.inr 2251, 8640), (Sum.inr 2253, 8640), (Sum.inr 2278, 8640), (Sum.inr 2751, 4320)]

def numericRow582 : Integer.Sparse Master := [(Sum.inl 0, -111), (Sum.inl 2, 160), (Sum.inl 3, 80), (Sum.inl 13, 80), (Sum.inl 1, 175), (Sum.inr 1406, 2160), (Sum.inr 3077, 1080), (Sum.inr 3078, 1080), (Sum.inr 3179, 1080), (Sum.inr 3180, 2160), (Sum.inr 3202, 2160), (Sum.inr 3221, 1080), (Sum.inr 3222, 2160)]

def numericRow583 : Integer.Sparse Master := [(Sum.inr 1040, 1), (Sum.inr 1042, 2), (Sum.inr 1079, 1), (Sum.inr 2262, 1), (Sum.inr 4084, -1)]

def numericRow584 : Integer.Sparse Master := [(Sum.inl 0, 19), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, 110), (Sum.inr 1041, -4320), (Sum.inr 1046, -2160), (Sum.inr 1050, -2160), (Sum.inr 1724, -4320), (Sum.inr 1750, -2160), (Sum.inr 1751, -2160), (Sum.inr 2020, -4320), (Sum.inr 2025, -4320), (Sum.inr 2029, -4320), (Sum.inr 2107, -4320), (Sum.inr 2112, -2160), (Sum.inr 2116, -2160), (Sum.inr 2202, -4320), (Sum.inr 2224, -4320), (Sum.inr 2225, -4320), (Sum.inr 2244, -4320), (Sum.inr 2247, -2160), (Sum.inr 2260, -4320), (Sum.inr 2262, -4320), (Sum.inr 2287, -2160), (Sum.inr 2288, -2160), (Sum.inr 2290, -2160), (Sum.inr 2739, -4320), (Sum.inr 2782, -2160), (Sum.inr 3534, -4320), (Sum.inr 3583, -2160), (Sum.inr 3623, -2160), (Sum.inr 4083, 8640)]

def numericRow585 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 1, -110), (Sum.inr 1724, 4320), (Sum.inr 1750, 2160), (Sum.inr 1751, 2160), (Sum.inr 2202, 4320), (Sum.inr 2224, 4320), (Sum.inr 2225, 4320), (Sum.inr 2260, 4320), (Sum.inr 2262, 4320), (Sum.inr 2287, 2160), (Sum.inr 2288, 2160), (Sum.inr 2290, 2160), (Sum.inr 2739, 4320), (Sum.inr 2782, 2160), (Sum.inr 4083, 2160)]

def numericRow586 : Integer.Sparse Master := [(Sum.inr 2107, 2), (Sum.inr 2112, 1), (Sum.inr 2116, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def numericRow587 : Integer.Sparse Master := [(Sum.inl 0, 43), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, -70), (Sum.inr 1079, -4320), (Sum.inr 1083, -2160), (Sum.inr 1087, -2160), (Sum.inr 1708, -4320), (Sum.inr 1728, -2160), (Sum.inr 1739, -2160), (Sum.inr 2051, -4320), (Sum.inr 2054, -4320), (Sum.inr 2058, -4320), (Sum.inr 2191, -4320), (Sum.inr 2206, -4320), (Sum.inr 2216, -4320), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2266, -4320), (Sum.inr 2277, -4320), (Sum.inr 2278, -4320), (Sum.inr 2279, -4320), (Sum.inr 2723, -4320), (Sum.inr 3544, -4320), (Sum.inr 3627, -2160), (Sum.inr 3632, -2160), (Sum.inr 4084, 8640)]

def numericRow588 : Integer.Sparse Master := [(Sum.inl 0, 4), (Sum.inl 2, -5), (Sum.inl 1, -5), (Sum.inr 1040, -720), (Sum.inr 1043, -360), (Sum.inr 1049, -360), (Sum.inr 1707, -720), (Sum.inr 1725, -360), (Sum.inr 1738, -360), (Sum.inr 2019, -720), (Sum.inr 2022, -720), (Sum.inr 2028, -720), (Sum.inr 2106, -720), (Sum.inr 2109, -360), (Sum.inr 2115, -360), (Sum.inr 2190, -720), (Sum.inr 2203, -720), (Sum.inr 2215, -720), (Sum.inr 2242, -720), (Sum.inr 2244, -720), (Sum.inr 2261, -360), (Sum.inr 2262, -720), (Sum.inr 2266, -360), (Sum.inr 2276, -360), (Sum.inr 2278, -360), (Sum.inr 2722, -720), (Sum.inr 2765, -360), (Sum.inr 3533, -720), (Sum.inr 3582, -360), (Sum.inr 3627, -360), (Sum.inr 4084, 1440)]

def numericRow589 : Integer.Sparse Master := [(Sum.inl 0, 1), (Sum.inl 2, -1), (Sum.inl 3, 16), (Sum.inl 1, 2), (Sum.inr 1083, -432), (Sum.inr 1091, -144), (Sum.inr 1728, -432), (Sum.inr 1756, -144), (Sum.inr 2054, -864), (Sum.inr 2062, -432), (Sum.inr 2206, -864), (Sum.inr 2230, -432), (Sum.inr 2266, -432), (Sum.inr 2278, -432), (Sum.inr 2281, -144), (Sum.inr 2294, -144), (Sum.inr 2743, -432), (Sum.inr 3548, -432), (Sum.inr 3633, -144), (Sum.inr 4084, 576)]

def numericRow590 : Integer.Sparse Master := [(Sum.inl 0, -3), (Sum.inl 1, -5), (Sum.inr 4069, 120), (Sum.inr 4070, 40), (Sum.inr 4071, 40), (Sum.inr 4080, 240), (Sum.inr 4081, 120), (Sum.inr 4082, 120), (Sum.inr 4083, 120), (Sum.inr 4084, 160), (Sum.inr 4085, 40), (Sum.inr 4092, 120)]

def numericRow591 : Integer.Sparse Master := [(Sum.inl 0, -604), (Sum.inl 5, -160), (Sum.inl 6, 20), (Sum.inl 2, -30), (Sum.inl 7, 320), (Sum.inl 35, 320), (Sum.inl 3, 640), (Sum.inl 13, 160), (Sum.inl 52, 320), (Sum.inl 12, 320), (Sum.inl 1, 290), (Sum.inr 1210, 17280), (Sum.inr 1216, 8640), (Sum.inr 1228, 8640), (Sum.inr 1260, 8640), (Sum.inr 2860, 17280), (Sum.inr 2864, 8640), (Sum.inr 2874, 8640), (Sum.inr 2984, 17280), (Sum.inr 3016, 17280), (Sum.inr 3023, 8640), (Sum.inr 3037, 8640), (Sum.inr 3086, 17280), (Sum.inr 3097, 17280), (Sum.inr 3801, 8640), (Sum.inr 3954, 8640)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow592 : Integer.Sparse Master := [(Sum.inl 0, -104), (Sum.inl 2, -15), (Sum.inl 3, 480), (Sum.inl 13, 240), (Sum.inl 12, 320), (Sum.inl 1, -75), (Sum.inr 3285, 8640), (Sum.inr 3286, 4320), (Sum.inr 3288, 4320), (Sum.inr 3289, 4320), (Sum.inr 3459, 4320), (Sum.inr 3460, 4320), (Sum.inr 3463, 8640), (Sum.inr 3524, 4320), (Sum.inr 3526, 4320), (Sum.inr 3527, 8640), (Sum.inr 3528, 8640), (Sum.inr 3533, 8640), (Sum.inr 3534, 8640), (Sum.inr 3540, 8640), (Sum.inr 3566, 4320), (Sum.inr 3567, 4320), (Sum.inr 3572, 8640), (Sum.inr 3800, 4320), (Sum.inr 3846, 4320)]

def numericRow593 : Integer.Sparse Master := [(Sum.inr 3805, 1), (Sum.inr 3812, 1), (Sum.inr 3874, 1), (Sum.inr 3903, 2), (Sum.inr 4092, -1)]

def numericRow594 : Integer.Sparse Master := [(Sum.inr 1212, 1), (Sum.inr 1214, 2), (Sum.inr 1233, 1), (Sum.inr 1259, 1), (Sum.inr 4092, -1)]

def numericRow595 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 2630, 1), (Sum.inr 2757, 1), (Sum.inr 2763, 2), (Sum.inr 4092, -1)]

def numericRow596 : Integer.Sparse Master := [(Sum.inr 2479, 1), (Sum.inr 2481, 2), (Sum.inr 2508, 1), (Sum.inr 3805, 1), (Sum.inr 4092, -1)]

def numericRow597 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 2739, 2), (Sum.inr 4092, -1)]

def numericRow598 : Integer.Sparse Master := [(Sum.inr 2614, 1), (Sum.inr 2616, 2), (Sum.inr 2630, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

def numericRow599 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, 13), (Sum.inl 3, -16), (Sum.inl 1, 40), (Sum.inr 2020, -1728), (Sum.inr 2202, -1728), (Sum.inr 2244, -864), (Sum.inr 2262, -864), (Sum.inr 2721, -2592), (Sum.inr 2739, -1728), (Sum.inr 2764, -864), (Sum.inr 3532, -2592), (Sum.inr 3534, -1728), (Sum.inr 3581, -864), (Sum.inr 3622, -864), (Sum.inr 3623, -864), (Sum.inr 4792, 3456), (Sum.inr 4795, 3456), (Sum.inr 5066, 3456), (Sum.inr 5077, 6912), (Sum.inr 5226, 6912), (Sum.inr 5230, 3456), (Sum.inr 5255, 13824), (Sum.inr 5262, 6912), (Sum.inr 5263, 3456), (Sum.inr 5265, 3456), (Sum.inr 5270, 3456), (Sum.inr 5289, 6912)]

def numericRow600 : Integer.Sparse Master := [(Sum.inl 0, -41), (Sum.inl 2, -25), (Sum.inl 3, 80), (Sum.inl 1, -140), (Sum.inr 2201, 1440), (Sum.inr 2202, 2880), (Sum.inr 2213, 1440), (Sum.inr 2262, 1440), (Sum.inr 2668, 1440), (Sum.inr 2669, 2880), (Sum.inr 2675, 1440), (Sum.inr 2717, 2880), (Sum.inr 2718, 2880), (Sum.inr 2721, 2880), (Sum.inr 2727, 2880), (Sum.inr 2730, 1440), (Sum.inr 2738, 1440), (Sum.inr 2739, 2880), (Sum.inr 2763, 2880), (Sum.inr 3036, 1440), (Sum.inr 3084, 2880)]

def numericRow601 : Integer.Sparse Master := [(Sum.inl 0, -588), (Sum.inl 5, -400), (Sum.inl 6, 60), (Sum.inl 2, -330), (Sum.inl 35, 320), (Sum.inl 8, 320), (Sum.inl 3, 1920), (Sum.inl 13, 480), (Sum.inl 52, 320), (Sum.inl 56, -960), (Sum.inl 26, 640), (Sum.inl 4, 640), (Sum.inl 1, -1570), (Sum.inr 2471, 8640), (Sum.inr 2472, 8640), (Sum.inr 2484, 17280), (Sum.inr 2718, 17280), (Sum.inr 2721, 8640), (Sum.inr 2728, 8640), (Sum.inr 2754, 8640), (Sum.inr 2764, 8640), (Sum.inr 3034, 17280), (Sum.inr 3037, 8640), (Sum.inr 3041, 8640), (Sum.inr 3084, 17280), (Sum.inr 3091, 17280), (Sum.inr 3097, 17280), (Sum.inr 3199, 8640)]

def numericRow602 : Integer.Sparse Master := [(Sum.inr 3503, 2), (Sum.inr 3505, 1), (Sum.inr 3532, 1), (Sum.inr 3581, 1), (Sum.inr 4083, -1)]

def numericRow603 : Integer.Sparse Master := [(Sum.inr 2980, 1), (Sum.inr 3373, 1), (Sum.inr 3376, 2), (Sum.inr 3505, 1), (Sum.inr 4083, -1)]

def numericRow604 : Integer.Sparse Master := [(Sum.inr 2012, 1), (Sum.inr 3373, 1), (Sum.inr 3500, 2), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def numericRow605 : Integer.Sparse Master := [(Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 3503, 1), (Sum.inr 3532, 1), (Sum.inr 3534, 1), (Sum.inr 4083, -1)]

def numericRow606 : Integer.Sparse Master := [(Sum.inr 2983, 1), (Sum.inr 3500, 1), (Sum.inr 3503, 2), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def numericRow607 : Integer.Sparse Master := [(Sum.inl 0, -185), (Sum.inl 5, 20), (Sum.inl 6, -10), (Sum.inl 2, -5), (Sum.inl 35, 80), (Sum.inl 3, 320), (Sum.inl 13, 240), (Sum.inl 52, 160), (Sum.inl 4, 160), (Sum.inl 1, 270), (Sum.inr 1178, 8640), (Sum.inr 1180, 4320), (Sum.inr 1183, 4320), (Sum.inr 1260, 4320), (Sum.inr 2833, 8640), (Sum.inr 2834, 4320), (Sum.inr 2836, 4320), (Sum.inr 2974, 8640), (Sum.inr 2976, 4320), (Sum.inr 3016, 8640), (Sum.inr 3023, 4320), (Sum.inr 3038, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3526, 4320), (Sum.inr 3801, 4320)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow608 : Integer.Sparse Master := [(Sum.inl 0, -16), (Sum.inl 2, -1), (Sum.inl 3, 64), (Sum.inl 13, 48), (Sum.inl 4, 32), (Sum.inl 1, 35), (Sum.inr 2833, 1728), (Sum.inr 2834, 864), (Sum.inr 2836, 864), (Sum.inr 3037, 864), (Sum.inr 3238, 1728), (Sum.inr 3239, 864), (Sum.inr 3241, 864), (Sum.inr 3289, 864), (Sum.inr 3460, 864), (Sum.inr 3461, 864), (Sum.inr 3464, 1728), (Sum.inr 3528, 1728), (Sum.inr 3534, 1728), (Sum.inr 3535, 1728), (Sum.inr 3541, 1728), (Sum.inr 3567, 864), (Sum.inr 3573, 1728), (Sum.inr 3801, 864)]

def numericRow609 : Integer.Sparse Master := [(Sum.inr 2730, 2), (Sum.inr 3812, 2), (Sum.inr 3906, 2), (Sum.inr 4092, -1)]

def numericRow610 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2757, 1), (Sum.inr 2773, 2), (Sum.inr 4092, -1)]

def numericRow611 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2494, 2), (Sum.inr 2508, 1), (Sum.inr 2730, 1), (Sum.inr 3812, 1), (Sum.inr 4092, -1)]

def numericRow612 : Integer.Sparse Master := [(Sum.inl 0, 17), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 12, 40), (Sum.inl 4, 80), (Sum.inl 1, -50), (Sum.inr 2880, -2160), (Sum.inr 3053, -2160), (Sum.inr 3617, -2160), (Sum.inr 3619, -2160), (Sum.inr 3849, -4320), (Sum.inr 3875, -4320), (Sum.inr 3910, -2160), (Sum.inr 3957, -4320), (Sum.inr 4406, 8640), (Sum.inr 4407, 17280), (Sum.inr 4414, 8640), (Sum.inr 4473, 8640), (Sum.inr 5004, 8640), (Sum.inr 5005, 17280), (Sum.inr 5011, 8640), (Sum.inr 5150, 17280), (Sum.inr 5184, 8640), (Sum.inr 5185, 17280), (Sum.inr 5243, 17280), (Sum.inr 5244, 17280), (Sum.inr 5265, 17280), (Sum.inr 5266, 17280), (Sum.inr 5270, 8640), (Sum.inr 5429, 8640)]

def numericRow613 : Integer.Sparse Master := [(Sum.inl 0, -70), (Sum.inl 5, 60), (Sum.inl 6, -15), (Sum.inl 2, 225), (Sum.inl 51, -720), (Sum.inl 3, 640), (Sum.inl 52, 240), (Sum.inl 4, 400), (Sum.inl 1, -370), (Sum.inl 31, -480), (Sum.inr 987, 4320), (Sum.inr 988, 8640), (Sum.inr 995, 4320), (Sum.inr 1056, 4320), (Sum.inr 2389, 4320), (Sum.inr 2390, 8640), (Sum.inr 2396, 4320), (Sum.inr 2614, 4320), (Sum.inr 2615, 8640), (Sum.inr 2697, 8640), (Sum.inr 2698, 8640), (Sum.inr 2700, 8640), (Sum.inr 2730, 8640), (Sum.inr 2731, 8640), (Sum.inr 2738, 4320), (Sum.inr 3874, 4320), (Sum.inr 3875, 8640)]

def numericRow614 : Integer.Sparse Master := [(Sum.inl 0, -16), (Sum.inl 2, 50), (Sum.inl 3, 640), (Sum.inl 12, 280), (Sum.inl 25, -240), (Sum.inl 26, 160), (Sum.inl 4, 400), (Sum.inl 1, -230), (Sum.inr 1593, 2160), (Sum.inr 1594, 2160), (Sum.inr 1601, 4320), (Sum.inr 1699, 2160), (Sum.inr 2912, 2160), (Sum.inr 2923, 4320), (Sum.inr 3075, 2160), (Sum.inr 3337, 2160), (Sum.inr 3342, 4320), (Sum.inr 3488, 4320), (Sum.inr 3497, 4320), (Sum.inr 3524, 2160), (Sum.inr 3526, 4320), (Sum.inr 3529, 4320), (Sum.inr 3535, 4320), (Sum.inr 3617, 2160), (Sum.inr 3619, 2160), (Sum.inr 3954, 2160), (Sum.inr 3957, 2160)]

def numericRow615 : Integer.Sparse Master := [(Sum.inr 3037, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 2), (Sum.inr 3910, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def numericRow616 : Integer.Sparse Master := [(Sum.inr 1358, 2), (Sum.inr 1360, 1), (Sum.inr 1366, 1), (Sum.inr 1421, 1), (Sum.inr 3037, 1), (Sum.inr 4091, -1)]

def numericRow617 : Integer.Sparse Master := [(Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 3), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

def numericRow618 : Integer.Sparse Master := [(Sum.inr 2862, 2), (Sum.inr 2864, 1), (Sum.inr 2880, 1), (Sum.inr 3037, 1), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

def numericRow619 : Integer.Sparse Master := [(Sum.inr 2573, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3037, 2), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

def numericRow620 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2023, -8640), (Sum.inr 2214, -8640), (Sum.inr 2245, -4320), (Sum.inr 2277, -4320), (Sum.inr 2671, -4320), (Sum.inr 2721, -12960), (Sum.inr 3053, -4320), (Sum.inr 3390, -4320), (Sum.inr 3532, -12960), (Sum.inr 3619, -4320), (Sum.inr 3622, -4320), (Sum.inr 4793, 17280), (Sum.inr 4794, 17280), (Sum.inr 4795, 17280), (Sum.inr 4806, 34560), (Sum.inr 4878, 17280), (Sum.inr 5226, 34560), (Sum.inr 5230, 17280), (Sum.inr 5231, 51840), (Sum.inr 5262, 34560), (Sum.inr 5263, 34560), (Sum.inr 5265, 34560), (Sum.inr 5299, 34560)]

def numericRow621 : Integer.Sparse Master := [(Sum.inl 0, -109), (Sum.inl 5, 60), (Sum.inl 2, -160), (Sum.inl 35, 240), (Sum.inl 3, 1040), (Sum.inl 55, -720), (Sum.inl 26, 640), (Sum.inl 4, 640), (Sum.inl 27, -180), (Sum.inl 1, -395), (Sum.inr 2117, 4320), (Sum.inr 2118, 8640), (Sum.inr 2131, 4320), (Sum.inr 2213, 4320), (Sum.inr 2214, 8640), (Sum.inr 2219, 4320), (Sum.inr 2277, 4320), (Sum.inr 2675, 4320), (Sum.inr 2676, 8640), (Sum.inr 2721, 8640), (Sum.inr 2727, 8640), (Sum.inr 2728, 8640), (Sum.inr 2730, 8640), (Sum.inr 2773, 8640), (Sum.inr 3043, 4320), (Sum.inr 3091, 8640)]

def numericRow622 : Integer.Sparse Master := [(Sum.inl 0, -169), (Sum.inl 5, -120), (Sum.inl 6, 20), (Sum.inl 2, -50), (Sum.inl 7, 160), (Sum.inl 35, 480), (Sum.inl 3, 1840), (Sum.inl 13, 1200), (Sum.inl 52, 320), (Sum.inl 54, -480), (Sum.inl 12, 560), (Sum.inl 26, 320), (Sum.inl 4, 320), (Sum.inl 1, -525), (Sum.inr 2010, 4320), (Sum.inr 2011, 4320), (Sum.inr 2024, 8640), (Sum.inr 2234, 4320), (Sum.inr 2669, 8640), (Sum.inr 2671, 4320), (Sum.inr 2676, 4320), (Sum.inr 2721, 4320), (Sum.inr 3034, 8640), (Sum.inr 3036, 8640), (Sum.inr 3037, 8640), (Sum.inr 3041, 4320), (Sum.inr 3043, 8640), (Sum.inr 3051, 8640), (Sum.inr 3053, 4320), (Sum.inr 3199, 4320)]

def numericRow623 : Integer.Sparse Master := [(Sum.inr 3376, 2), (Sum.inr 3378, 1), (Sum.inr 3390, 1), (Sum.inr 3526, 1), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow624 : Integer.Sparse Master := [(Sum.inr 3150, 1), (Sum.inr 3373, 1), (Sum.inr 3378, 3), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def numericRow625 : Integer.Sparse Master := [(Sum.inr 2010, 1), (Sum.inr 3149, 2), (Sum.inr 3150, 1), (Sum.inr 3155, 1), (Sum.inr 3526, 1), (Sum.inr 4083, -1)]

def numericRow626 : Integer.Sparse Master := [(Sum.inr 2023, 1), (Sum.inr 3378, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 2), (Sum.inr 3532, 1), (Sum.inr 4083, -1)]

def numericRow627 : Integer.Sparse Master := [(Sum.inr 3149, 1), (Sum.inr 3376, 1), (Sum.inr 3500, 1), (Sum.inr 3505, 1), (Sum.inr 3526, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow628 : Integer.Sparse Master := [(Sum.inl 0, 116), (Sum.inl 2, -10), (Sum.inl 3, 160), (Sum.inl 12, -40), (Sum.inl 1, 530), (Sum.inr 1293, -2160), (Sum.inr 1294, -2160), (Sum.inr 2954, -4320), (Sum.inr 3053, -2160), (Sum.inr 3054, -2160), (Sum.inr 3304, -2160), (Sum.inr 3305, -2160), (Sum.inr 3308, -1080), (Sum.inr 3603, -2160), (Sum.inr 3606, -4320), (Sum.inr 3619, -2160), (Sum.inr 3623, -4320), (Sum.inr 3626, -2160), (Sum.inr 3633, -2160), (Sum.inr 3902, -2160)]

def numericRow629 : Integer.Sparse Master := [(Sum.inl 0, -53), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 1, -250), (Sum.inr 1293, 1080), (Sum.inr 1294, 1080), (Sum.inr 2954, 2160), (Sum.inr 3053, 1080), (Sum.inr 3054, 1080)]

def numericRow630 : Integer.Sparse Master := [(Sum.inl 0, 118), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, -80), (Sum.inl 1, -95), (Sum.inr 1079, -2160), (Sum.inr 1080, -1080), (Sum.inr 1083, -2160), (Sum.inr 1708, -2160), (Sum.inr 1710, -1080), (Sum.inr 1728, -2160), (Sum.inr 2508, -2160), (Sum.inr 2509, -2160), (Sum.inr 2512, -4320), (Sum.inr 2704, -2160), (Sum.inr 2739, -4320), (Sum.inr 2740, -4320), (Sum.inr 2743, -2160), (Sum.inr 3460, -2160), (Sum.inr 3471, -4320), (Sum.inr 3534, -4320), (Sum.inr 3548, -2160), (Sum.inr 3622, -2160), (Sum.inr 3627, -2160), (Sum.inr 4010, -2160)]

def numericRow631 : Integer.Sparse Master := [(Sum.inl 0, -19), (Sum.inl 2, 1), (Sum.inl 3, -16), (Sum.inl 1, 16), (Sum.inr 1079, 432), (Sum.inr 1080, 216), (Sum.inr 1083, 432), (Sum.inr 2508, 432), (Sum.inr 2509, 432), (Sum.inr 2512, 864), (Sum.inr 2739, 864), (Sum.inr 2740, 432), (Sum.inr 2743, 432)]

def numericRow632 : Integer.Sparse Master := [(Sum.inl 0, 47), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -20), (Sum.inr 2244, -4320), (Sum.inr 2247, -2160), (Sum.inr 2262, -4320), (Sum.inr 2290, -2160), (Sum.inr 2739, -8640), (Sum.inr 2764, -4320), (Sum.inr 2782, -8640), (Sum.inr 3534, -8640), (Sum.inr 3581, -4320), (Sum.inr 3583, -8640), (Sum.inr 3622, -4320), (Sum.inr 5270, 17280), (Sum.inr 5289, 34560), (Sum.inr 5295, 17280)]

def numericRow633 : Integer.Sparse Master := [(Sum.inl 0, -47), (Sum.inl 2, -55), (Sum.inl 3, -80), (Sum.inl 1, 20), (Sum.inr 2754, 1080), (Sum.inr 2764, 1080), (Sum.inr 2769, 1080), (Sum.inr 2782, 1080), (Sum.inr 3097, 2160)]

def numericRow634 : Integer.Sparse Master := [(Sum.inr 3581, 2), (Sum.inr 3583, 2), (Sum.inr 3623, 1), (Sum.inr 4083, -1)]

def numericRow635 : Integer.Sparse Master := [(Sum.inl 0, -206), (Sum.inl 2, -30), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 200), (Sum.inr 1228, 4320), (Sum.inr 1229, 4320), (Sum.inr 1230, 4320), (Sum.inr 1241, 4320), (Sum.inr 1291, 4320), (Sum.inr 2874, 4320), (Sum.inr 2875, 4320), (Sum.inr 2876, 4320), (Sum.inr 2885, 4320), (Sum.inr 2921, 4320), (Sum.inr 2922, 4320), (Sum.inr 2928, 4320), (Sum.inr 2951, 4320), (Sum.inr 3023, 4320), (Sum.inr 3024, 4320), (Sum.inr 3025, 4320), (Sum.inr 3051, 4320), (Sum.inr 3086, 4320), (Sum.inr 3097, 4320), (Sum.inr 3098, 4320), (Sum.inr 3809, 4320), (Sum.inr 3959, 4320), (Sum.inr 3972, 4320)]

def numericRow636 : Integer.Sparse Master := [(Sum.inl 0, -106), (Sum.inl 2, -65), (Sum.inl 3, -160), (Sum.inl 13, -80), (Sum.inl 12, -160), (Sum.inl 1, 205), (Sum.inr 2500, 4320), (Sum.inr 2502, 4320), (Sum.inr 2506, 4320), (Sum.inr 2513, 4320), (Sum.inr 2781, 4320), (Sum.inr 3286, 4320), (Sum.inr 3287, 4320), (Sum.inr 3296, 4320), (Sum.inr 3303, 4320), (Sum.inr 3533, 4320), (Sum.inr 3534, 4320), (Sum.inr 3540, 4320), (Sum.inr 3557, 4320), (Sum.inr 3558, 4320), (Sum.inr 3560, 4320), (Sum.inr 3566, 4320), (Sum.inr 3567, 4320), (Sum.inr 3570, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3575, 4320), (Sum.inr 3577, 4320), (Sum.inr 3582, 4320), (Sum.inr 3583, 4320), (Sum.inr 3871, 4320), (Sum.inr 3881, 4320)]

def numericRow637 : Integer.Sparse Master := [(Sum.inr 2763, 1), (Sum.inr 3813, 1), (Sum.inr 3848, 1), (Sum.inr 3884, 1), (Sum.inr 3903, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

def numericRow638 : Integer.Sparse Master := [(Sum.inr 1259, 1), (Sum.inr 1261, 1), (Sum.inr 1263, 1), (Sum.inr 1268, 1), (Sum.inr 1291, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

def numericRow639 : Integer.Sparse Master := [(Sum.inr 2566, 1), (Sum.inr 2568, 1), (Sum.inr 2571, 1), (Sum.inr 2587, 1), (Sum.inr 2763, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow64 : Integer.Sparse Master := [(Sum.inr 1224, 1), (Sum.inr 2495, 1), (Sum.inr 2547, 1), (Sum.inr 2647, 1), (Sum.inr 2731, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

def numericRow65 : Integer.Sparse Master := [(Sum.inr 1359, 1), (Sum.inr 2547, 1), (Sum.inr 2558, 1), (Sum.inr 2579, 1), (Sum.inr 2734, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

def numericRow66 : Integer.Sparse Master := [(Sum.inr 1243, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 2), (Sum.inr 2734, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

def numericRow67 : Integer.Sparse Master := [(Sum.inr 1424, 1), (Sum.inr 2647, 2), (Sum.inr 2651, 1), (Sum.inr 2734, 1), (Sum.inr 2777, 1), (Sum.inr 4092, -1)]

def numericRow68 : Integer.Sparse Master := [(Sum.inr 1227, 1), (Sum.inr 1359, 2), (Sum.inr 1372, 1), (Sum.inr 1424, 1), (Sum.inr 2734, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow640 : Integer.Sparse Master := [(Sum.inr 1291, 1), (Sum.inr 2587, 1), (Sum.inr 2739, 1), (Sum.inr 2763, 1), (Sum.inr 2773, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

def numericRow641 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2632, 1), (Sum.inr 2634, 1), (Sum.inr 2639, 1), (Sum.inr 2763, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

def numericRow642 : Integer.Sparse Master := [(Sum.inl 0, 49), (Sum.inl 2, -5), (Sum.inl 3, 80), (Sum.inl 4, 160), (Sum.inl 1, -50), (Sum.inr 2954, -4320), (Sum.inr 3077, -4320), (Sum.inr 3606, -4320), (Sum.inr 3625, -4320), (Sum.inr 3857, -4320), (Sum.inr 3876, -4320), (Sum.inr 3983, -17280), (Sum.inr 4010, -4320), (Sum.inr 4449, 17280), (Sum.inr 4450, 17280), (Sum.inr 4453, 17280), (Sum.inr 4459, 17280), (Sum.inr 4487, 17280), (Sum.inr 5069, 17280), (Sum.inr 5071, 17280), (Sum.inr 5074, 17280), (Sum.inr 5092, 17280), (Sum.inr 5140, 17280), (Sum.inr 5160, 17280), (Sum.inr 5161, 34560), (Sum.inr 5164, 17280), (Sum.inr 5226, 17280), (Sum.inr 5229, 17280), (Sum.inr 5236, 17280), (Sum.inr 5255, 17280), (Sum.inr 5260, 17280), (Sum.inr 5269, 17280), (Sum.inr 5281, 17280), (Sum.inr 5282, 17280), (Sum.inr 5289, 17280), (Sum.inr 5480, 17280)]

def numericRow643 : Integer.Sparse Master := [(Sum.inl 0, -98), (Sum.inl 5, -20), (Sum.inl 6, 5), (Sum.inl 2, 45), (Sum.inl 7, -80), (Sum.inl 35, -80), (Sum.inl 3, -400), (Sum.inl 13, -160), (Sum.inl 12, -160), (Sum.inl 26, -80), (Sum.inl 4, -160), (Sum.inl 1, -30), (Sum.inr 1032, 4320), (Sum.inr 1033, 4320), (Sum.inr 1036, 4320), (Sum.inr 1042, 4320), (Sum.inr 1071, 4320), (Sum.inr 2476, 4320), (Sum.inr 2478, 4320), (Sum.inr 2481, 4320), (Sum.inr 2501, 4320), (Sum.inr 2587, 4320), (Sum.inr 2588, 4320), (Sum.inr 2591, 4320), (Sum.inr 2669, 4320), (Sum.inr 2670, 4320), (Sum.inr 2673, 4320), (Sum.inr 2682, 4320), (Sum.inr 2718, 4320), (Sum.inr 2719, 4320), (Sum.inr 2724, 4320), (Sum.inr 2736, 4320), (Sum.inr 2750, 4320), (Sum.inr 2751, 4320), (Sum.inr 2763, 4320), (Sum.inr 3857, 4320), (Sum.inr 3978, 4320), (Sum.inr 3983, 4320)]

def numericRow644 : Integer.Sparse Master := [(Sum.inl 0, -84), (Sum.inl 2, 20), (Sum.inl 3, -480), (Sum.inl 12, -80), (Sum.inl 26, -160), (Sum.inl 4, -320), (Sum.inl 1, 120), (Sum.inr 1636, 4320), (Sum.inr 1637, 4320), (Sum.inr 1641, 4320), (Sum.inr 1646, 4320), (Sum.inr 1714, 4320), (Sum.inr 2550, 4320), (Sum.inr 2560, 4320), (Sum.inr 2588, 4320), (Sum.inr 2719, 4320), (Sum.inr 3376, 4320), (Sum.inr 3380, 4320), (Sum.inr 3392, 4320), (Sum.inr 3442, 4320), (Sum.inr 3445, 4320), (Sum.inr 3463, 4320), (Sum.inr 3503, 4320), (Sum.inr 3507, 4320), (Sum.inr 3540, 4320), (Sum.inr 3558, 4320), (Sum.inr 3565, 4320), (Sum.inr 3571, 4320), (Sum.inr 3572, 4320), (Sum.inr 3580, 4320), (Sum.inr 3606, 4320), (Sum.inr 3625, 4320), (Sum.inr 3978, 4320), (Sum.inr 3983, 4320)]

def numericRow645 : Integer.Sparse Master := [(Sum.inr 3097, 1), (Sum.inr 3876, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

def numericRow646 : Integer.Sparse Master := [(Sum.inr 1403, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3084, 1), (Sum.inr 3091, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

def numericRow647 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 2964, 1), (Sum.inr 3097, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

def numericRow648 : Integer.Sparse Master := [(Sum.inr 2942, 1), (Sum.inr 3091, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 3115, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

def numericRow649 : Integer.Sparse Master := [(Sum.inl 0, -290), (Sum.inl 2, -270), (Sum.inl 3, 160), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, -340), (Sum.inr 2240, 8640), (Sum.inr 2259, 8640), (Sum.inr 2260, 8640), (Sum.inr 2262, 8640), (Sum.inr 2274, 8640), (Sum.inr 2583, 8640), (Sum.inr 2584, 8640), (Sum.inr 2585, 8640), (Sum.inr 2600, 8640), (Sum.inr 2717, 8640), (Sum.inr 2718, 8640), (Sum.inr 2727, 8640), (Sum.inr 2749, 8640), (Sum.inr 2750, 8640), (Sum.inr 2760, 8640), (Sum.inr 2762, 8640), (Sum.inr 2763, 17280), (Sum.inr 2764, 8640), (Sum.inr 2772, 8640), (Sum.inr 2773, 8640), (Sum.inr 2781, 8640), (Sum.inr 2782, 8640), (Sum.inr 3084, 8640), (Sum.inr 3108, 8640)]

def numericRow650 : Integer.Sparse Master := [(Sum.inr 2952, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3534, 1), (Sum.inr 3572, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def numericRow651 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2950, 1), (Sum.inr 3550, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

def numericRow652 : Integer.Sparse Master := [(Sum.inr 2094, 1), (Sum.inr 2956, 1), (Sum.inr 3500, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

def numericRow653 : Integer.Sparse Master := [(Sum.inr 2950, 1), (Sum.inr 2952, 1), (Sum.inr 2956, 1), (Sum.inr 2962, 1), (Sum.inr 3096, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

def numericRow654 : Integer.Sparse Master := [(Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 3503, 1), (Sum.inr 3572, 1), (Sum.inr 3581, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

def numericRow655 : Integer.Sparse Master := [(Sum.inr 2995, 1), (Sum.inr 3507, 1), (Sum.inr 3550, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

def numericRow656 : Integer.Sparse Master := [(Sum.inl 0, 301), (Sum.inl 2, -110), (Sum.inl 3, -160), (Sum.inl 12, 40), (Sum.inl 1, -395), (Sum.inr 1235, -2160), (Sum.inr 1236, -4320), (Sum.inr 1240, -2160), (Sum.inr 2880, -2160), (Sum.inr 2881, -4320), (Sum.inr 2884, -2160), (Sum.inr 2924, -4320), (Sum.inr 3077, -4320), (Sum.inr 3292, -2160), (Sum.inr 3293, -4320), (Sum.inr 3299, -2160), (Sum.inr 3307, -2160), (Sum.inr 3602, -2160), (Sum.inr 3605, -4320), (Sum.inr 3617, -2160), (Sum.inr 3621, -2160), (Sum.inr 3622, -6480), (Sum.inr 3624, -4320), (Sum.inr 3625, -4320), (Sum.inr 3627, -4320), (Sum.inr 3632, -4320), (Sum.inr 3901, -2160), (Sum.inr 3910, -2160)]

def numericRow657 : Integer.Sparse Master := [(Sum.inl 0, -133), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, 160), (Sum.inr 1235, 1080), (Sum.inr 1236, 2160), (Sum.inr 1240, 1080), (Sum.inr 2880, 1080), (Sum.inr 2881, 2160), (Sum.inr 2884, 1080), (Sum.inr 2924, 2160), (Sum.inr 3077, 2160)]

def numericRow658 : Integer.Sparse Master := [(Sum.inl 0, 677), (Sum.inl 2, -165), (Sum.inl 3, -240), (Sum.inl 4, 160), (Sum.inl 1, 90), (Sum.inr 1039, -4320), (Sum.inr 1040, -4320), (Sum.inr 1041, -8640), (Sum.inr 1079, -4320), (Sum.inr 1706, -4320), (Sum.inr 1707, -4320), (Sum.inr 1708, -4320), (Sum.inr 1724, -8640), (Sum.inr 2479, -4320), (Sum.inr 2480, -8640), (Sum.inr 2508, -4320), (Sum.inr 2721, -8640), (Sum.inr 2722, -8640), (Sum.inr 2723, -8640), (Sum.inr 2739, -8640), (Sum.inr 3459, -4320), (Sum.inr 3460, -4320), (Sum.inr 3467, -8640), (Sum.inr 3532, -8640), (Sum.inr 3533, -8640), (Sum.inr 3534, -8640), (Sum.inr 3544, -8640), (Sum.inr 3602, -4320), (Sum.inr 3603, -4320), (Sum.inr 3607, -8640), (Sum.inr 3622, -4320), (Sum.inr 3623, -4320), (Sum.inr 3627, -8640), (Sum.inr 4046, -4320)]

def numericRow659 : Integer.Sparse Master := [(Sum.inl 0, -181), (Sum.inl 2, 55), (Sum.inl 3, 80), (Sum.inl 1, -80), (Sum.inr 1039, 1440), (Sum.inr 1040, 1440), (Sum.inr 1041, 2880), (Sum.inr 1079, 1440), (Sum.inr 2479, 1440), (Sum.inr 2480, 2880), (Sum.inr 2508, 1440), (Sum.inr 2721, 2880), (Sum.inr 2722, 2880), (Sum.inr 2723, 2880), (Sum.inr 2739, 2880)]

def numericRow660 : Integer.Sparse Master := [(Sum.inl 0, 179), (Sum.inl 2, 175), (Sum.inl 3, 80), (Sum.inl 1, 160), (Sum.inr 2243, -8640), (Sum.inr 2244, -4320), (Sum.inr 2245, -4320), (Sum.inr 2262, -4320), (Sum.inr 2277, -4320), (Sum.inr 2721, -12960), (Sum.inr 2739, -8640), (Sum.inr 2764, -8640), (Sum.inr 3053, -4320), (Sum.inr 3532, -12960), (Sum.inr 3534, -8640), (Sum.inr 3581, -8640), (Sum.inr 3619, -4320), (Sum.inr 3622, -12960), (Sum.inr 3623, -4320), (Sum.inr 5265, 17280), (Sum.inr 5281, 34560), (Sum.inr 5289, 34560), (Sum.inr 5299, 34560)]

def numericRow661 : Integer.Sparse Master := [(Sum.inr 3532, 1), (Sum.inr 3534, 2), (Sum.inr 3622, 1), (Sum.inr 4083, -1)]

def numericRow662 : Integer.Sparse Master := [(Sum.inr 2243, 1), (Sum.inr 3571, 2), (Sum.inr 3622, 2), (Sum.inr 4083, -1)]

def numericRow663 : Integer.Sparse Master := [(Sum.inl 0, -252), (Sum.inl 2, -200), (Sum.inl 26, 160), (Sum.inl 4, 160), (Sum.inl 1, 180), (Sum.inr 1183, 8640), (Sum.inr 1184, 8640), (Sum.inr 1185, 8640), (Sum.inr 1189, 8640), (Sum.inr 1291, 8640), (Sum.inr 2836, 8640), (Sum.inr 2837, 8640), (Sum.inr 2838, 8640), (Sum.inr 2841, 8640), (Sum.inr 2906, 8640), (Sum.inr 2907, 8640), (Sum.inr 2909, 8640), (Sum.inr 2951, 8640), (Sum.inr 3023, 8640), (Sum.inr 3024, 8640), (Sum.inr 3025, 8640), (Sum.inr 3037, 8640), (Sum.inr 3038, 8640), (Sum.inr 3039, 8640), (Sum.inr 3051, 8640), (Sum.inr 3052, 8640), (Sum.inr 3055, 8640), (Sum.inr 3097, 8640), (Sum.inr 3535, 8640), (Sum.inr 3809, 8640), (Sum.inr 3839, 8640)]

def numericRow664 : Integer.Sparse Master := [(Sum.inl 0, -88), (Sum.inl 2, -60), (Sum.inl 3, -240), (Sum.inl 13, -80), (Sum.inl 12, -160), (Sum.inl 4, -80), (Sum.inl 1, 180), (Sum.inr 2463, 4320), (Sum.inr 2465, 4320), (Sum.inr 2466, 4320), (Sum.inr 2513, 4320), (Sum.inr 2744, 4320), (Sum.inr 2834, 4320), (Sum.inr 2835, 4320), (Sum.inr 2841, 4320), (Sum.inr 3039, 4320), (Sum.inr 3239, 4320), (Sum.inr 3240, 4320), (Sum.inr 3246, 4320), (Sum.inr 3303, 4320), (Sum.inr 3526, 4320), (Sum.inr 3534, 4320), (Sum.inr 3535, 4320), (Sum.inr 3541, 4320), (Sum.inr 3558, 4320), (Sum.inr 3559, 4320), (Sum.inr 3561, 4320), (Sum.inr 3567, 4320), (Sum.inr 3572, 4320), (Sum.inr 3573, 4320), (Sum.inr 3577, 4320), (Sum.inr 3583, 4320), (Sum.inr 3584, 4320), (Sum.inr 3872, 4320)]

def numericRow665 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 1277, 1), (Sum.inr 1278, 1), (Sum.inr 1280, 1), (Sum.inr 1291, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

def numericRow666 : Integer.Sparse Master := [(Sum.inl 0, 18), (Sum.inl 2, 5), (Sum.inl 3, -80), (Sum.inl 4, -80), (Sum.inl 1, -25), (Sum.inr 2881, -2160), (Sum.inr 3054, -2160), (Sum.inr 3624, -2160), (Sum.inr 3626, -2160), (Sum.inr 3850, -4320), (Sum.inr 3857, -2160), (Sum.inr 3876, -2160), (Sum.inr 3913, -2160), (Sum.inr 3958, -2160), (Sum.inr 3961, -2160), (Sum.inr 4469, 8640), (Sum.inr 4470, 8640), (Sum.inr 4471, 8640), (Sum.inr 4475, 8640), (Sum.inr 4486, 8640), (Sum.inr 5082, 8640), (Sum.inr 5083, 8640), (Sum.inr 5086, 8640), (Sum.inr 5091, 8640), (Sum.inr 5151, 8640), (Sum.inr 5173, 8640), (Sum.inr 5197, 8640), (Sum.inr 5198, 8640), (Sum.inr 5199, 8640), (Sum.inr 5231, 8640), (Sum.inr 5232, 8640), (Sum.inr 5233, 8640), (Sum.inr 5263, 8640), (Sum.inr 5264, 8640), (Sum.inr 5267, 8640), (Sum.inr 5295, 8640), (Sum.inr 5299, 8640), (Sum.inr 5300, 8640), (Sum.inr 5430, 8640)]

def numericRow669 : Integer.Sparse Master := [(Sum.inr 3051, 1), (Sum.inr 3848, 1), (Sum.inr 3850, 1), (Sum.inr 3857, 1), (Sum.inr 3913, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_OriginalBlock1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock1 : Integer.Sparse (Fin 2886) := [(32, 10028624640), (33, -13312972800), (34, -7014424320), (35, -1862481600), (36, 11656704000), (37, -20552948400), (38, 1541328000), (39, 2449074240), (40, 3078374400), (41, -1541328000), (42, -33813990720), (43, 6613813440), (44, 10849711680), (45, -13312972800), (46, -2022739200), (47, 3936988800), (48, 1545425280), (49, 1686608640), (50, 1545425280), (51, 522207360), (52, 762128640), (53, -3936988800), (54, 188943200), (55, -1686608640), (56, -340097760), (57, -4636275840), (58, -1044414720), (59, -1333725120), (60, 7368592000), (61, -10105497600), (62, -762128640), (63, -11656704000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1001 : Integer.Sparse Master := [(Sum.inr 2687, 2753869669962743808000), (Sum.inr 2688, 2124806707563724800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


