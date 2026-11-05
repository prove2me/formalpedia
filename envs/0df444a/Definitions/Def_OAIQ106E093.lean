-- Prove2me | Definitions.Def_OAIQ106E093
-- name    : OAIQ106E093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:05:12.402318+00:00
-- url     : https://prove2.me/theorems/a47f75bc-b839-4104-af92-350985130d01
-- title:
--   Definitions bundle OAIQ106E093 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7330 declarations of OpenAI's Lean: 7330 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw17035step2`, `OAI.MUB6.Certificate.MixedSemantics.raw17036`, `OAI.MUB6.Certificate.MixedSemantics.raw17036Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17036step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17036step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17037`, `OAI.MUB6.Certificate.MixedSemantics.raw17037Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step2`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step3`, `OAI.MUB6.Certificate.MixedSemantics.raw17037step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17038`, `OAI.MUB6.Certificate.MixedSemantics.raw17038Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17038step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17038step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17038step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17038step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17039`, `OAI.MUB6.Certificate.MixedSemantics.raw17039Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17039step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17039step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17039step1`, `OAI.MUB6.Certificate.MixedSemantics.raw17039step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1703Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step0`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step1`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step2`, `OAI.MUB6.Certificate.MixedSemantics.raw1703step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw1704`, `OAI.MUB6.Certificate.MixedSemantics.raw17040`, `OAI.MUB6.Certificate.MixedSemantics.raw17040Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17040step0`, `OAI.MUB6.Certificate.MixedSemantics.raw17040step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw17040step1` and 7290 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical13.lean), [`MutuallyUnbiased_MixedSemantics_Canonical133`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical133.lean), [`MutuallyUnbiased_MixedSemantics_Canonical134`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical134.lean), [`MutuallyUnbiased_MixedSemantics_Canonical135`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical135.lean), [`MutuallyUnbiased_MixedSemantics_Canonical136`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical136.lean), [`MutuallyUnbiased_MixedSemantics_Canonical137`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical137.lean), [`MutuallyUnbiased_MixedSemantics_Canonical138`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical138.lean), [`MutuallyUnbiased_MixedSemantics_Canonical139`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical139.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical140`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical140.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound57_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1978_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2004_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2022_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2086_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound897_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound900_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound913_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound918_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound919_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound920_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound927_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound928_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound929_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound931_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound933_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound39_e`.
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

def raw17Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw17step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw17step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw18 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]

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

def raw170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw171 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw171step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw171step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw174 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw175 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw175step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw175step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw176 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw177 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 1, 0], ![-1, 3, -2]]
def raw177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw177step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw177step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw180 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1703Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1704 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1705 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1706 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1706Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1707 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1708 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1709 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1709Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1712Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1715Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1718Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1721Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1722 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1723 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1724 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1724Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1727Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1728 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1729 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1730 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1730Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1733Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw1733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1736Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw1736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1737 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1738 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1739 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1739Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw1739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1742Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1743 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1744 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1745 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1745Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1746 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1747 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1748 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1748Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw1748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1749 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1750 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1751 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1751Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1754Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1755 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1756 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1757 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1757Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1758 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1759 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1760 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1760Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1763Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1763step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1764 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1765 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1766 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1766Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw1766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1767 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1768 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1769 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1769Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1770 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1771 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1772 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1772Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw1772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1773 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1774 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1775 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1775Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1776 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1777 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1778 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1778Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw1778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1781Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1782 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1783 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1784 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1784Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1785 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1786 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1787 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1787Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1790Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1791 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]

def raw17036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17041step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17042step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17043step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17044 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17044step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17049 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17052step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17054 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17055 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17056 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17057 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17058 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw17064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw17069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17088step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17097step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17098step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17098step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17098step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17099step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17102step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17102step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17102step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17106step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw17106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw17109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw17119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17120 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17124step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17125step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17126step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17126step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw17178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw17206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17215step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17223 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17224 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17229 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17231step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17233 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17235 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17235step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17236 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17241step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17281step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17285step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17287step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw17287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw17302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw17311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17313 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw17313Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw17313step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17313step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17313step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17317step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17320step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17331step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17337step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17338step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw17352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17376 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17379step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17388step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17389step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17393 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17395 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17396 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17397 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17398 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17399 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw17404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical136
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17409 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17414 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17415 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17416 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw17417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17425step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17436step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17437step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17438step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw17463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17469 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw17469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17472 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17475step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17478step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17479step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17485step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17486 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17488step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17492step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17494 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17495 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17496 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17497 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17501 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17505 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17506 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17509 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17513 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17517 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical137
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17543step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17569step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17575Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw17576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17577Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17579Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17580step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17582step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17602step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17603step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17604step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw17614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw17614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17633step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17634step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17637step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17653 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17666step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw17679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw17680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17680step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]
def raw17686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw17686step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw17686step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw17698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw17702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17702step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw17702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17711step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17721step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17730step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw17731step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17732step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw17753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17809step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17811step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17812step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17814step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17826 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17827 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17832 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw17839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw17847step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17847step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17875step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17876 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17876step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17879step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]
def raw17881step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17883step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17902step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17907step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17912step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw17913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1792 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1793 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1793Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw1793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1794 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1795 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1796 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1796Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1797 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1798 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1799 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1799Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw1799step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1800 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1801 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1802 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17921step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17921step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17924step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17926step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17926step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17927step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17928step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17929step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17931step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17931step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17931step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17931step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17933step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17936step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17937step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw17938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17947step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17948step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17948step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17952step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17952step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17959step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -2, 0]]
def raw17961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0]]
def raw17962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17962step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17964step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw17966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw17967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw17969step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -2, 0]]
def raw17970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw17971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw17972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0]]
def raw17972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw17973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw17974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw17975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17975step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw17976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw17977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -3, 0]]
def raw17977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17982step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17982step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17984step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw17986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw17987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17987step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw17996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw17997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17997step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw17999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw17999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18003step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw18004step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18004step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw18004step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18005step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18006step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18006step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18007step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18007step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw18016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw18017step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end


